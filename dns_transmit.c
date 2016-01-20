#include <sys/types.h>
#include <sys/socket.h>
#include <unistd.h>
#include "socket.h"
#include "alloc.h"
#include "error.h"
#include "byte.h"
#include "uint16.h"
#include "dns.h"
#include "ip6.h"

#define NSCACHED 512 /* too large means no expiration which would be bad. */
#define RESOLUTION 1000 /* 1000 means milliseconds. should be <max_uint32/45 */
struct nscache {
  char ip[16];
  uint32 used;
} nsc[NSCACHED];
unsigned int nsc_idx=0;

static void nsc_reserve(const struct dns_transmit *d, unsigned int timeout)
{
  /* reserve a slot in the array for d->remoteip */
  unsigned int i;
  for (i=0;i<NSCACHED;i++) {
    unsigned int j=(i+nsc_idx)%NSCACHED;
    if (byte_equal(nsc[j].ip,16,d->remoteip)) {
      nsc[j].used=timeout*RESOLUTION;
      if (j!=nsc_idx) {
	struct nscache t;
	t=nsc[nsc_idx];
	nsc[nsc_idx]=nsc[j];
	nsc[j]=t;
      }
      nsc_idx=(nsc_idx+1)%NSCACHED;
      return;
    }
  }
  byte_copy(nsc[nsc_idx].ip,16,d->remoteip);
  nsc[nsc_idx].used=timeout*RESOLUTION;
  nsc_idx=(nsc_idx+1)%NSCACHED;
}

static void nsc_good(const struct dns_transmit *d)
{
  struct taia t;
  unsigned long x;
  unsigned int i;
  taia_now(&t);
  taia_sub(&t,&t,&d->start);
  x=taia_approx(&t)*RESOLUTION;
  for (i=0;i<NSCACHED;i++)
    if (byte_equal(d->remoteip,16,nsc[i].ip))
      nsc[i].used=x;
}

void dns_reorder(char *buf, unsigned int len)
{
  /* servers are already randomized */
  unsigned int x=len/16;
  uint32 *y;
  unsigned int i;
  unsigned int j;
  if (!nsc) _exit(77);
  if (x<2) return;
  y=(uint32 *)alloc(sizeof(uint32) * x);
  if (!y) return;

  for (j=0;j<x;j++) {
    if (byte_equal(buf+16*j,16,V6any))
      y[j]=0x7fffffff;
    else {
      for (i=0;i<NSCACHED;i++) {
	if (byte_equal(nsc[i].ip,16,buf+16*j)) {
	  y[j]=nsc[i].used;
	  break;
	}
      }
      if (i==NSCACHED) /* unknown. Could be fast. */
	y[j]=0;
    }
  }
  /* hyper fast bubble sort. */
  for (i=0;i<x-1;i++) {
    for (j=i+1;j<x;j++) {
      if (y[j]<y[i]) {
	uint32 t;
	char ip[16];
	t=y[i]; y[i]=y[j];y[j]=t;
	byte_copy(ip,16,buf+i*16);
	byte_copy(buf+i*16,16,buf+j*16);
	byte_copy(buf+j*16,16,ip);
      }
    }
  }
}

static int serverwantstcp(const char *buf,unsigned int len)
{
  char out[12];

  if (!dns_packet_copy(buf,len,0,out,12)) return 1;
  if (out[2] & 2) return 1;
  return 0;
}

static int serverfailed(const char *buf,unsigned int len)
{
  char out[12];
  unsigned int rcode;

  if (!dns_packet_copy(buf,len,0,out,12)) return 1;
  rcode = out[3];
  rcode &= 15;
  if (rcode && (rcode != 3)) { errno = error_again; return 1; }
  return 0;
}

static int irrelevant(const struct dns_transmit *d,const char *buf,unsigned int len)
{
  char out[12];
  char *dn;
  unsigned int pos;

  pos = dns_packet_copy(buf,len,0,out,12); if (!pos) return 1;
  if (byte_diff(out,2,d->query + 2)) return 1;
  if (out[4] != 0) return 1;
  if (out[5] != 1) return 1;

  dn = 0;
  pos = dns_packet_getname(buf,len,pos,&dn); if (!pos) return 1;
  if (!dns_domain_equal(dn,d->query + 14)) { alloc_free(dn); return 1; }
  alloc_free(dn);

  pos = dns_packet_copy(buf,len,pos,out,4); if (!pos) return 1;
  if (byte_diff(out,2,d->qtype)) return 1;
  if (byte_diff(out + 2,2,DNS_C_IN)) return 1;

  return 0;
}

static void packetfree(struct dns_transmit *d)
{
  if (!d->packet) return;
  alloc_free(d->packet);
  d->packet = 0;
}

static void queryfree(struct dns_transmit *d)
{
  if (!d->query) return;
  alloc_free(d->query);
  d->query = 0;
}

static void socketfree(struct dns_transmit *d)
{
  if (!d->s1) return;
  close(d->s1 - 1);
  d->s1 = 0;
}

void dns_transmit_free(struct dns_transmit *d)
{
  queryfree(d);
  socketfree(d);
  packetfree(d);
}

static int randombind(struct dns_transmit *d)
{
  int j;

  for (j = 0;j < 10;++j)
    if (socket_bind6(d->s1 - 1,d->localip,1025 + dns_random(64510),d->scope_id) == 0)
      return 0;
  if (socket_bind6(d->s1 - 1,d->localip,0,d->scope_id) == 0)
    return 0;
  return -1;
}

static const int timeouts[4] = { 1, 3, 11, 45 };

static int thisudp(struct dns_transmit *d)
{
  const char *ip;

  socketfree(d);

  while (d->udploop < 4) {
    for (;d->curserver < 16;++d->curserver) {
      ip = d->servers + 16 * d->curserver;
      if (byte_diff(ip,16,V6any)) {
	d->query[2] = dns_random(256);
	d->query[3] = dns_random(256);
  
        d->s1 = 1 + socket_udp6();
        if (!d->s1) { dns_transmit_free(d); return -1; }
	if (randombind(d) == -1) { dns_transmit_free(d); return -1; }

        if (socket_connect6(d->s1 - 1,ip,53,d->scope_id) == 0)
          if (send(d->s1 - 1,d->query + 2,d->querylen - 2,0) == d->querylen - 2) {
            struct taia now;
            taia_now(&now);
            taia_uint(&d->deadline,timeouts[d->udploop]);
            taia_add(&d->deadline,&d->deadline,&now);
            d->tcpstate = 0;
	    d->start=now;
	    byte_copy(d->remoteip,16,ip);
	    nsc_reserve(d,timeouts[d->udploop]);
            return 0;
          }
  
        socketfree(d);
      }
    }

    ++d->udploop;
    d->curserver = 0;
  }

  dns_transmit_free(d); return -1;
}

static int firstudp(struct dns_transmit *d)
{
  d->curserver = 0;
  return thisudp(d);
}

static int nextudp(struct dns_transmit *d)
{
  ++d->curserver;
  return thisudp(d);
}

static int thistcp(struct dns_transmit *d)
{
  struct taia now;
  const char *ip;

  socketfree(d);
  packetfree(d);

  for (;d->curserver < 16;++d->curserver) {
    ip = d->servers + 16 * d->curserver;
    if (byte_diff(ip,16,V6any)) {
      d->query[2] = dns_random(256);
      d->query[3] = dns_random(256);

      d->s1 = 1 + socket_tcp6();
      if (!d->s1) { dns_transmit_free(d); return -1; }
      if (randombind(d) == -1) { dns_transmit_free(d); return -1; }
  
      taia_now(&now);
      taia_uint(&d->deadline,10);
      taia_add(&d->deadline,&d->deadline,&now);
      if (socket_connect6(d->s1 - 1,ip,53,d->scope_id) == 0) {
	d->pos = 0;
        d->tcpstate = 2;
        return 0;
      }
      if ((errno == error_inprogress) || (errno == error_wouldblock)) {
        d->tcpstate = 1;
        return 0;
      }
  
      socketfree(d);
    }
  }

  dns_transmit_free(d); return -1;
}

static int firsttcp(struct dns_transmit *d)
{
  d->curserver = 0;
  return thistcp(d);
}

static int nexttcp(struct dns_transmit *d)
{
  ++d->curserver;
  return thistcp(d);
}

int dns_transmit_start(struct dns_transmit *d,const char servers[256],int flagrecursive,const char *q,const char qtype[2],const char localip[16])
{
  unsigned int len;

  dns_transmit_free(d);
  errno = error_io;

  len = dns_domain_length(q);
  d->querylen = len + 18;
  d->query = alloc(d->querylen);
  if (!d->query) return -1;

  uint16_pack_big(d->query,len + 16);
  byte_copy(d->query + 2,12,flagrecursive ? "\0\0\1\0\0\1\0\0\0\0\0\0" : "\0\0\0\0\0\1\0\0\0\0\0\0gcc-bug-workaround");
  byte_copy(d->query + 14,len,q);
  byte_copy(d->query + 14 + len,2,qtype);
  byte_copy(d->query + 16 + len,2,DNS_C_IN);

  byte_copy(d->qtype,2,qtype);
  d->servers = servers;
  byte_copy(d->localip,16,localip);

  d->udploop = flagrecursive ? 1 : 0;

  if (len + 16 > 512) return firsttcp(d);
  return firstudp(d);
}

void dns_transmit_io(struct dns_transmit *d,iopause_fd *x,struct taia *deadline)
{
  x->fd = d->s1 - 1;

  switch(d->tcpstate) {
    case 0: case 3: case 4: case 5:
      x->events = IOPAUSE_READ;
      break;
    case 1: case 2:
      x->events = IOPAUSE_WRITE;
      break;
  }

  if (taia_less(&d->deadline,deadline))
    *deadline = d->deadline;
}

int dns_transmit_get(struct dns_transmit *d,const iopause_fd *x,const struct taia *when)
{
  char udpbuf[4097];
  unsigned char ch;
  int r;
  int fd;

  errno = error_io;
  fd = d->s1 - 1;

  if (!x->revents) {
    if (taia_less(when,&d->deadline)) return 0;
    errno = error_timeout;
    if (d->tcpstate == 0) return nextudp(d);
    return nexttcp(d);
  }

  if (d->tcpstate == 0) {
/*
have attempted to send UDP query to each server udploop times
have sent query to curserver on UDP socket s
*/
    r = recv(fd,udpbuf,sizeof udpbuf,0);
    if (r <= 0) {
      if (errno == error_connrefused) if (d->udploop == 2) return 0;
      return nextudp(d);
    }
    if (r + 1 > sizeof udpbuf) return 0;

    if (irrelevant(d,udpbuf,r)) return 0;
    nsc_good(d);
    if (serverwantstcp(udpbuf,r)) return firsttcp(d);
    if (serverfailed(udpbuf,r)) {
      if (d->udploop == 2) return 0;
      return nextudp(d);
    }
    socketfree(d);

    d->packetlen = r;
    d->packet = alloc(d->packetlen);
    if (!d->packet) { dns_transmit_free(d); return -1; }
    byte_copy(d->packet,d->packetlen,udpbuf);
    queryfree(d);
    return 1;
  }

  if (d->tcpstate == 1) {
/*
have sent connection attempt to curserver on TCP socket s
pos not defined
*/
    if (!socket_connected(fd)) return nexttcp(d);
    d->pos = 0;
    d->tcpstate = 2;
    return 0;
  }

  if (d->tcpstate == 2) {
/*
have connection to curserver on TCP socket s
have sent pos bytes of query
*/
    r = write(fd,d->query + d->pos,d->querylen - d->pos);
    if (r <= 0) return nexttcp(d);
    d->pos += r;
    if (d->pos == d->querylen) {
      struct taia now;
      taia_now(&now);
      taia_uint(&d->deadline,10);
      taia_add(&d->deadline,&d->deadline,&now);
      d->tcpstate = 3;
    }
    return 0;
  }

  if (d->tcpstate == 3) {
/*
have sent entire query to curserver on TCP socket s
pos not defined
*/
    r = read(fd,&ch,1);
    if (r <= 0) return nexttcp(d);
    d->packetlen = ch;
    d->tcpstate = 4;
    return 0;
  }

  if (d->tcpstate == 4) {
/*
have sent entire query to curserver on TCP socket s
pos not defined
have received one byte of packet length into packetlen
*/
    r = read(fd,&ch,1);
    if (r <= 0) return nexttcp(d);
    d->packetlen <<= 8;
    d->packetlen += ch;
    d->tcpstate = 5;
    d->pos = 0;
    d->packet = alloc(d->packetlen);
    if (!d->packet) { dns_transmit_free(d); return -1; }
    return 0;
  }

  if (d->tcpstate == 5) {
/*
have sent entire query to curserver on TCP socket s
have received entire packet length into packetlen
packet is allocated
have received pos bytes of packet
*/
    r = read(fd,d->packet + d->pos,d->packetlen - d->pos);
    if (r <= 0) return nexttcp(d);
    d->pos += r;
    if (d->pos < d->packetlen) return 0;

    socketfree(d);
    if (irrelevant(d,d->packet,d->packetlen)) return nexttcp(d);
    if (serverwantstcp(d->packet,d->packetlen)) return nexttcp(d);
    if (serverfailed(d->packet,d->packetlen)) return nexttcp(d);

    queryfree(d);
    return 1;
  }

  return 0;
}
