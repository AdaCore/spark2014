/*
 * Copyright (c) 2001-2003 Swedish Institute of Computer Science.
 * All rights reserved. 
 * 
 * Redistribution and use in source and binary forms, with or without modification, 
 * are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission. 
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR IMPLIED 
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF 
 * MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT 
 * SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, 
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT 
 * OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS 
 * INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN 
 * CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING 
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY 
 * OF SUCH DAMAGE.
 *
 * This file is part of the lwIP TCP/IP stack.
 * 
 * Author: Adam Dunkels <adam@sics.se>
 *
 */

#include <string.h>
#include <stdio.h>

#include "lwip/mem.h"
#include "lwip/debug.h"
#include "lwip/def.h"
#include "lwip/api.h"
#include "lwip/stats.h"
#include "lwip/inet.h"

static unsigned char buffer[1024];

struct command {
  struct netconn *conn;
  s8_t (* exec)(struct command *);
  u8_t nargs;
  char *args[10];
};

#undef IP_HDRINCL

#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include <limits.h>

#define ESUCCESS 0
#define ESYNTAX -1
#define ETOOFEW -2
#define ETOOMANY -3
#define ECLOSED -4

#define NCONNS 10
static struct netconn *conns[NCONNS];

static char help_msg[] = "Available commands:\n\
open [IP address] [TCP port]: opens a TCP connection to the specified address.\n\
lstn [TCP port]: sets up a server on the specified port.\n\
acpt [connection #]: waits for an incoming connection request.\n\
send [connection #] [message]: sends a message on a TCP connection.\n\
udpc [local UDP port] [IP address] [remote port]: opens a UDP \"connection\".\n\
udpl [local UDP port] [IP address] [remote port]: opens a UDP-Lite \"connection\".\n\
udpn [local UDP port] [IP address] [remote port]: opens a UDP \"connection\" without checksums.\n\
udpb [local port] [remote port]: opens a UDP broadcast \"connection\".\n\
usnd [connection #] [message]: sends a message on a UDP connection.\n\
recv [connection #]: recieves data on a TCP or UDP connection.\n\
clos [connection #]: closes a TCP or UDP connection.\n\
stat: prints out lwIP statistics.\n\
quit: quits.\n";

#define STAT_NUM ((6 * 13) + (6) + (4) + (11 * 4) + (2 * 3))

static char *stat_msgs[STAT_NUM] = {
  "Link level * transmitted ",
  "             retransmitted ",
  "           * received ",
  "             forwarded ",
  "           * dropped ",
  "           * checksum errors ",
  "           * length errors ",
  "           * memory errors ",
  "             routing errors ",
  "             protocol errors ",
  "             option errors ",
  "           * misc errors ",
  "             cache hits ",  
  "IP_FRAG    * transmitted ",
  "             retransmitted ",
  "           * received ",
  "           * forwarded ",
  "           * dropped ",
  "           * checksum errors ",
  "           * length errors ",
  "           * memory errors ",
  "           * routing errors ",
  "           * protocol errors ",
  "           * option errors ",
  "           * misc errors ",
  "             cache hits ",
  "IP         * transmitted ",
  "             retransmitted ",
  "           * received ",
  "           * forwarded ",
  "           * dropped ",
  "           * checksum errors ",
  "           * length errors ",
  "           * memory errors ",
  "           * routing errors ",
  "           * protocol errors ",
  "           * option errors ",
  "           * misc errors ",
  "             cache hits ",
  "ICMP       * transmitted ",
  "             retransmitted ",
  "           * received ",
  "             forwarded ",
  "           * dropped ",
  "           * checksum errors ",
  "             length errors ",
  "           * memory errors ",
  "             routing errors ",
  "           * protocol errors ",
  "             option errors ",
  "           * misc errors ",
  "             cache hits ",  
  "UDP        * transmitted ",
  "             retransmitted ",
  "           * received ",
  "             forwarded ",
  "           * dropped ",
  "           * checksum errors ",
  "           * length errors ",
  "           * memory errors ",
  "           * routing errors ",
  "           * protocol errors ",
  "             option errors ",
  "           * misc errors ",
  "             cache hits ",  
  "TCP        * transmitted ",
  "           * retransmitted ",
  "           * received ",
  "             forwarded ",
  "           * dropped ",
  "           * checksum errors ",
  "           * length errors ",
  "           * memory errors ",
  "           * routing errors ",
  "           * protocol errors ",
  "           * option errors ",
  "           * misc errors ",
  "           * cache hits ",  
  "Pbufs      * available ",
  "           * used ",
  "           * high water mark ",
  "           * errors ",
  "             pbuf_alloc() locked ",
  "             pbuf_refresh() locked ",
  "Memory     * available ",
  "           * used ",
  "           * high water mark ",
  "           * errors ",
  "Memp PBUF  * available ",
  "           * used ",
  "           * high water mark ",
  "           * errors ",
  "RAW PCB    * available ",
  "           * used ",
  "           * high water mark ",
  "           * errors ",
  "UDP PCB    * available ",
  "           * used ",
  "           * high water mark ",
  "           * errors ",
  "TCP PCB    * available ",
  "           * used ",
  "           * high water mark ",
  "           * errors ",
  "TCP LISTEN * available ",
  "           * used ",
  "           * high water mark ",
  "           * errors ",
  "TCP SEG    * available ",
  "           * used ",
  "           * high water mark ",
  "           * errors ",
  "Netbufs    * available ",
  "           * used ",
  "           * high water mark ",
  "           * errors ",
  "Netconns   * available ",
  "           * used ",
  "           * high water mark ",
  "           * errors ",
  "API msgs   * available ",
  "           * used ",
  "           * high water mark ",
  "           * errors ",
  "TCPIP msgs * available ",
  "           * used ",
  "           * high water mark ",
  "           * errors ",
  "Timeouts   * available ",
  "           * used ",
  "           * high water mark ",
  "           * errors ",
  "Semaphores * used ",
  "           * high water mark ",
  "           * errors ",
  "Mailboxes  * used ",
  "           * high water mark ",
  "           * errors "
};

static char *stat_formats[STAT_NUM] = {
  U16_F, /* link xmit */
  U16_F, /* link rexmit */
  U16_F, /* link recv */
  U16_F, /* link fw */ 
  U16_F, /* link drop */
  U16_F, /* link chkerr */
  U16_F, /* link lenerr */
  U16_F, /* link memerr */
  U16_F, /* link rterr */
  U16_F, /* link proterr */
  U16_F, /* link opterr */
  U16_F, /* link err */
  U16_F, /* link cachehit */

  U16_F, /* ip_frag xmit */
  U16_F, /* ip_frag rexmit */
  U16_F, /* ip_frag recv */
  U16_F, /* ip_frag fw */ 
  U16_F, /* ip_frag drop */
  U16_F, /* ip_frag chkerr */
  U16_F, /* ip_frag lenerr */
  U16_F, /* ip_frag memerr */
  U16_F, /* ip_frag rterr */
  U16_F, /* ip_frag proterr */
  U16_F, /* ip_frag opterr */
  U16_F, /* ip_frag err */
  U16_F, /* ip_frag cachehit */

  U16_F, /* ip xmit */
  U16_F, /* ip rexmit */
  U16_F, /* ip recv */
  U16_F, /* ip fw */ 
  U16_F, /* ip drop */
  U16_F, /* ip chkerr */
  U16_F, /* ip lenerr */
  U16_F, /* ip memerr */
  U16_F, /* ip rterr */
  U16_F, /* ip proterr */
  U16_F, /* ip opterr */
  U16_F, /* ip err */
  U16_F, /* ip cachehit */

  U16_F, /* icmp xmit */
  U16_F, /* icmp rexmit */
  U16_F, /* icmp recv */
  U16_F, /* icmp fw */ 
  U16_F, /* icmp drop */
  U16_F, /* icmp chkerr */
  U16_F, /* icmp lenerr */
  U16_F, /* icmp memerr */
  U16_F, /* icmp rterr */
  U16_F, /* icmp proterr */
  U16_F, /* icmp opterr */
  U16_F, /* icmp err */
  U16_F, /* icmp cachehit */

  U16_F, /* udp xmit */
  U16_F, /* udp rexmit */
  U16_F, /* udp recv */
  U16_F, /* udp fw */ 
  U16_F, /* udp drop */
  U16_F, /* udp chkerr */
  U16_F, /* udp lenerr */
  U16_F, /* udp memerr */
  U16_F, /* udp rterr */
  U16_F, /* udp proterr */
  U16_F, /* udp opterr */
  U16_F, /* udp err */
  U16_F, /* udp cachehit */  

  U16_F, /* tcp xmit */
  U16_F, /* tcp exmit */
  U16_F, /* tcp recv */
  U16_F, /* tcp fw */ 
  U16_F, /* tcp drop */
  U16_F, /* tcp chkerr */
  U16_F, /* tcp lenerr */
  U16_F, /* tcp memerr */
  U16_F, /* tcp rterr */
  U16_F, /* tcp proterr */
  U16_F, /* tcp opterr */
  U16_F, /* tcp err */
  U16_F, /* tcp cachehit */

  /* FIXME: pbuf stats have moved to memp stats */
  U16_F, /* pbuf avail */
  U16_F, /* pbuf used */
  U16_F, /* pbuf max */
  U16_F, /* pbuf err */
  U16_F, /* pbuf alloc_locked */
  U16_F, /* pbuf refresh_locked */

  /* FIXME: always using 11 memp pools is wrong! */
  U32_F, /* mem avail */
  U32_F, /* mem used */
  U32_F, /* mem max */
  U32_F, /* mem err */
  
  U32_F, /* memp pbuf avail */
  U32_F, /* memp pbuf used */
  U32_F, /* memp pbuf max */
  U32_F, /* memp pbuf err */

  U32_F, /* memp raw pcb avail */
  U32_F, /* memp raw pcb used */
  U32_F, /* memp raw pcb max */
  U32_F, /* memp raw err */

  U32_F, /* memp udp pcb avail */
  U32_F, /* memp udp pcb used */
  U32_F, /* memp udp pcb max */
  U32_F, /* memp udp pcb err */

  U32_F, /* memp tcp pcb avail */
  U32_F, /* memp tcp pcb used */
  U32_F, /* memp tcp pcb max */
  U32_F, /* memp tcp pcb err */

  U32_F, /* memp tcp lstn pcb avail */
  U32_F, /* memp tcp lstn pcb used */
  U32_F, /* memp tcp lstn pcb max */
  U32_F, /* memp tcp lstn pcb err */

  U32_F, /* memp tcp seg avail */
  U32_F, /* memp tcp seg used */
  U32_F, /* memp tcp seg max */
  U32_F, /* memp tcp seg err */

  U32_F, /* memp netbuf avail */
  U32_F, /* memp netbuf used */
  U32_F, /* memp netbuf max */
  U32_F, /* memp netbuf err */

  U32_F, /* memp netconn avail */
  U32_F, /* memp netconn used */
  U32_F, /* memp netconn max */
  U32_F, /* memp netconn err */

  U32_F, /* memp api msg avail */
  U32_F, /* memp api msg used */
  U32_F, /* memp api msg max */
  U32_F, /* memp api msg err */

  U32_F, /* memp tcpip msg avail */
  U32_F, /* memp tcpip msg used */
  U32_F, /* memp tcpip msg max */
  U32_F, /* memp tcpip msg err */

  U32_F, /* memp sys to avail */
  U32_F, /* memp sys to used */
  U32_F, /* memp sys to max */
  U32_F, /* memp sys to err */

  U16_F, /* sys sem used */
  U16_F, /* sys sem max */
  U16_F, /* sys sem err */

  U16_F, /* sys mbox used */
  U16_F, /* sys mbox max */
  U16_F, /* sys mbox err */
};

static void *stat_ptrs[STAT_NUM] = {
  &lwip_stats.link.xmit,
  &lwip_stats.link.rexmit,
  &lwip_stats.link.recv,
  &lwip_stats.link.fw,
  &lwip_stats.link.drop,
  &lwip_stats.link.chkerr,
  &lwip_stats.link.lenerr,
  &lwip_stats.link.memerr,
  &lwip_stats.link.rterr,
  &lwip_stats.link.proterr,
  &lwip_stats.link.opterr,
  &lwip_stats.link.err,
  &lwip_stats.link.cachehit,

  &lwip_stats.ip_frag.xmit,
  &lwip_stats.ip_frag.rexmit,
  &lwip_stats.ip_frag.recv,
  &lwip_stats.ip_frag.fw,
  &lwip_stats.ip_frag.drop,
  &lwip_stats.ip_frag.chkerr,
  &lwip_stats.ip_frag.lenerr,
  &lwip_stats.ip_frag.memerr,
  &lwip_stats.ip_frag.rterr,
  &lwip_stats.ip_frag.proterr,
  &lwip_stats.ip_frag.opterr,
  &lwip_stats.ip_frag.err,
  &lwip_stats.ip_frag.cachehit,

  &lwip_stats.ip.xmit,
  &lwip_stats.ip.rexmit,
  &lwip_stats.ip.recv,
  &lwip_stats.ip.fw,
  &lwip_stats.ip.drop,
  &lwip_stats.ip.chkerr,
  &lwip_stats.ip.lenerr,
  &lwip_stats.ip.memerr,
  &lwip_stats.ip.rterr,
  &lwip_stats.ip.proterr,
  &lwip_stats.ip.opterr,
  &lwip_stats.ip.err,
  &lwip_stats.ip.cachehit,

  &lwip_stats.icmp.xmit,
  &lwip_stats.icmp.rexmit,
  &lwip_stats.icmp.recv,
  &lwip_stats.icmp.fw,
  &lwip_stats.icmp.drop,
  &lwip_stats.icmp.chkerr,
  &lwip_stats.icmp.lenerr,
  &lwip_stats.icmp.memerr,
  &lwip_stats.icmp.rterr,
  &lwip_stats.icmp.proterr,
  &lwip_stats.icmp.opterr,
  &lwip_stats.icmp.err,
  &lwip_stats.icmp.cachehit,

  &lwip_stats.udp.xmit,
  &lwip_stats.udp.rexmit,
  &lwip_stats.udp.recv,
  &lwip_stats.udp.fw,
  &lwip_stats.udp.drop,
  &lwip_stats.udp.chkerr,
  &lwip_stats.udp.lenerr,
  &lwip_stats.udp.memerr,
  &lwip_stats.udp.rterr,
  &lwip_stats.udp.proterr,
  &lwip_stats.udp.opterr,
  &lwip_stats.udp.err,
  &lwip_stats.udp.cachehit,

  &lwip_stats.tcp.xmit,
  &lwip_stats.tcp.rexmit,
  &lwip_stats.tcp.recv,
  &lwip_stats.tcp.fw,
  &lwip_stats.tcp.drop,
  &lwip_stats.tcp.chkerr,
  &lwip_stats.tcp.lenerr,
  &lwip_stats.tcp.memerr,
  &lwip_stats.tcp.rterr,
  &lwip_stats.tcp.proterr,
  &lwip_stats.tcp.opterr,
  &lwip_stats.tcp.err,
  &lwip_stats.tcp.cachehit,

  /* FIXME: pbuf stats have moved to memp stats */
  NULL, NULL, NULL, NULL, NULL, NULL,
  /*&lwip_stats.pbuf.avail,
  &lwip_stats.pbuf.used,
  &lwip_stats.pbuf.max,
  &lwip_stats.pbuf.err,
  &lwip_stats.pbuf.alloc_locked,
  &lwip_stats.pbuf.refresh_locked,*/

  &lwip_stats.mem.avail,
  &lwip_stats.mem.used,
  &lwip_stats.mem.max,
  &lwip_stats.mem.err,

  /* FIXME: always using 11 memp pools is wrong! */
  &lwip_stats.memp[0].avail,
  &lwip_stats.memp[0].used,
  &lwip_stats.memp[0].max,
  &lwip_stats.memp[0].err,

  &lwip_stats.memp[1].avail,
  &lwip_stats.memp[1].used,
  &lwip_stats.memp[1].max,
  &lwip_stats.memp[1].err,

  &lwip_stats.memp[2].avail,
  &lwip_stats.memp[2].used,
  &lwip_stats.memp[2].max,
  &lwip_stats.memp[2].err,

  &lwip_stats.memp[3].avail,
  &lwip_stats.memp[3].used,
  &lwip_stats.memp[3].max,
  &lwip_stats.memp[3].err,

  &lwip_stats.memp[4].avail,
  &lwip_stats.memp[4].used,
  &lwip_stats.memp[4].max,
  &lwip_stats.memp[4].err,

  &lwip_stats.memp[5].avail,
  &lwip_stats.memp[5].used,
  &lwip_stats.memp[5].max,
  &lwip_stats.memp[5].err,

  &lwip_stats.memp[6].avail,
  &lwip_stats.memp[6].used,
  &lwip_stats.memp[6].max,
  &lwip_stats.memp[6].err,

  &lwip_stats.memp[7].avail,
  &lwip_stats.memp[7].used,
  &lwip_stats.memp[7].max,
  &lwip_stats.memp[7].err,

  &lwip_stats.memp[8].avail,
  &lwip_stats.memp[8].used,
  &lwip_stats.memp[8].max,
  &lwip_stats.memp[8].err,

  &lwip_stats.memp[9].avail,
  &lwip_stats.memp[9].used,
  &lwip_stats.memp[9].max,
  &lwip_stats.memp[9].err,

  &lwip_stats.memp[10].avail,
  &lwip_stats.memp[10].used,
  &lwip_stats.memp[10].max,
  &lwip_stats.memp[10].err,

  &lwip_stats.sys.sem.used,
  &lwip_stats.sys.sem.max,
  &lwip_stats.sys.sem.err,

  &lwip_stats.sys.mbox.used,
  &lwip_stats.sys.mbox.max,
  &lwip_stats.sys.mbox.err,
};

/*-----------------------------------------------------------------------------------*/
static void
sendstr(const char *str, struct netconn *conn)
{
  netconn_write(conn, (void *)str, strlen(str), NETCONN_NOCOPY);
}
/*-----------------------------------------------------------------------------------*/
static s8_t
com_open(struct command *com)
{
  struct ip_addr ipaddr;
  u16_t port;
  int i;
  err_t err;

  if (inet_aton(com->args[0], (struct in_addr *)&ipaddr) == -1) {
    sendstr(strerror(errno), com->conn);
    return ESYNTAX;
  }
  port = strtol(com->args[1], NULL, 10);

  /* Find the first unused connection in conns. */
  for(i = 0; i < NCONNS && conns[i] != NULL; i++);

  if (i == NCONNS) {
    sendstr("No more connections available, sorry.\n", com->conn);
    return ESUCCESS;
  }

  sendstr("Opening connection to ", com->conn);
  netconn_write(com->conn, com->args[0], strlen(com->args[0]), NETCONN_COPY);
  sendstr(":", com->conn);
  netconn_write(com->conn, com->args[1], strlen(com->args[1]), NETCONN_COPY);
  sendstr("\n", com->conn);

  conns[i] = netconn_new(NETCONN_TCP);
  if (conns[i] == NULL) {    
    sendstr("Could not create connection identifier (out of memory).\n", com->conn); 
    return ESUCCESS;
  }
  err = netconn_connect(conns[i], &ipaddr, port);
  if (err != ERR_OK) {
    fprintf(stderr, "error %s\n", lwip_strerr(err));
    sendstr("Could not connect to remote host: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(err), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    netconn_delete(conns[i]);
    conns[i] = NULL;
    return ESUCCESS;
  }

  sendstr("Opened connection, connection identifier is ", com->conn);
  snprintf((char *)buffer, sizeof(buffer), "%d\n", i);
  netconn_write(com->conn, buffer, strlen((const char *)buffer), NETCONN_COPY);
  
  return ESUCCESS;
}
/*-----------------------------------------------------------------------------------*/
static s8_t
com_lstn(struct command *com)
{
  u16_t port;
  int i;
  err_t err;

  port = strtol(com->args[0], NULL, 10);

  /* Find the first unused connection in conns. */
  for(i = 0; i < NCONNS && conns[i] != NULL; i++);

  if (i == NCONNS) {
    sendstr("No more connections available, sorry.\n", com->conn);
    return ESUCCESS;
  }

  sendstr("Opening a listening connection on port ", com->conn);
  netconn_write(com->conn, com->args[0], strlen(com->args[0]), NETCONN_COPY);
  sendstr("\n", com->conn);

  conns[i] = netconn_new(NETCONN_TCP);
  if (conns[i] == NULL) {    
    sendstr("Could not create connection identifier (out of memory).\n", com->conn); 
    return ESUCCESS;
  }
  
  err = netconn_bind(conns[i], IP_ADDR_ANY, port);
  if (err != ERR_OK) {
    netconn_delete(conns[i]);
    conns[i] = NULL;
    sendstr("Could not bind: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(err), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    return ESUCCESS;
  }
  
  err = netconn_listen(conns[i]);
  if (err != ERR_OK) {
    netconn_delete(conns[i]);
    conns[i] = NULL;
    sendstr("Could not listen: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(err), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    return ESUCCESS;
  }

  sendstr("Opened connection, connection identifier is ", com->conn);
  snprintf((char *)buffer, sizeof(buffer), "%d\n", i);
  netconn_write(com->conn, buffer, strlen((const char *)buffer), NETCONN_COPY);
  
  return ESUCCESS;
}
/*-----------------------------------------------------------------------------------*/
/*-----------------------------------------------------------------------------------*/
static s8_t
com_clos(struct command *com)
{
  int i;
  err_t err;
  
  i = strtol(com->args[0], NULL, 10);

  if (i > NCONNS) {
    sendstr("Connection identifier too high.\n", com->conn);
    return ESUCCESS;
  }
  if (conns[i] == NULL) {
    sendstr("Connection identifier not in use.\n", com->conn);
    return ESUCCESS;
  }

  err = netconn_close(conns[i]);
  if (err != ERR_OK) {
    sendstr("Could not close connection: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(err), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    return ESUCCESS;
  }

  sendstr("Connection closed.\n", com->conn);
  netconn_delete(conns[i]);
  conns[i] = NULL;
  return ESUCCESS;
}
/*-----------------------------------------------------------------------------------*/
static s8_t
com_acpt(struct command *com)
{
  int i, j;

  /* Find the first unused connection in conns. */
  for(j = 0; j < NCONNS && conns[j] != NULL; j++);

  if (j == NCONNS) {
    sendstr("No more connections available, sorry.\n", com->conn);
    return ESUCCESS;
  }

  i = strtol(com->args[0], NULL, 10);

  if (i > NCONNS) {
    sendstr("Connection identifier too high.\n", com->conn);
    return ESUCCESS;
  }
  if (conns[i] == NULL) {
    sendstr("Connection identifier not in use.\n", com->conn);
    return ESUCCESS;
  }

  conns[j] = netconn_accept(conns[i]);
  
  if (conns[j] == NULL) {
    sendstr("Could not accept connection: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(netconn_err(conns[i])), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    return ESUCCESS;
  }

  sendstr("Accepted connection, connection identifier for new connection is ", com->conn);
  snprintf((char *)buffer, sizeof(buffer), "%d\n", j);
  netconn_write(com->conn, buffer, strlen((const char *)buffer), NETCONN_COPY);

  return ESUCCESS;
}
/*-----------------------------------------------------------------------------------*/
#if LWIP_STATS
static s8_t
com_stat(struct command *com)
{
  int i;
  char fmt[10] = "%s%";
  char buf[100];
  u16_t len;
  
  for(i = 0; i < STAT_NUM; i++) {
    snprintf(&fmt[3], sizeof(fmt) - 3,"%s\n", stat_formats[i]);
    if (strcmp(stat_formats[i], U16_F) == 0) {
      len = snprintf(buf, sizeof(buf), fmt, stat_msgs[i], *(u16_t*)stat_ptrs[i]);    
    }
    else if (strcmp(stat_formats[i], U32_F) == 0) {
      len = snprintf(buf, sizeof(buf), fmt, stat_msgs[i], *(mem_size_t*)stat_ptrs[i]);
    }
    else {
      len = snprintf(buf, sizeof(buf), "%s %s", stat_msgs[i], "unkown format");
    }
    netconn_write(com->conn, buf, len, NETCONN_COPY);
  }

  return ESUCCESS;
}
#endif
/*-----------------------------------------------------------------------------------*/
static s8_t
com_send(struct command *com)
{
  int i;
  err_t err;
  int len;
  
  i = strtol(com->args[0], NULL, 10);

  if (i > NCONNS) {
    sendstr("Connection identifier too high.\n", com->conn);
    return ESUCCESS;
  }

  if (conns[i] == NULL) {
    sendstr("Connection identifier not in use.\n", com->conn);
    return ESUCCESS;
  }

  len = strlen(com->args[1]);
  com->args[1][len] = '\r';
  com->args[1][len + 1] = '\n';
  com->args[1][len + 2] = 0;
  
  err = netconn_write(conns[i], com->args[1], len + 3, NETCONN_COPY);
  if (err != ERR_OK) {
    sendstr("Could not send data: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(err), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    return ESUCCESS;
  }
  
  sendstr("Data enqueued for sending.\n", com->conn);
  return ESUCCESS;
}
/*-----------------------------------------------------------------------------------*/
static s8_t
com_recv(struct command *com)
{
  int i;
  err_t err;
  struct netbuf *buf;
  u16_t len;
  
  i = strtol(com->args[0], NULL, 10);

  if (i > NCONNS) {
    sendstr("Connection identifier too high.\n", com->conn);
    return ESUCCESS;
  }

  if (conns[i] == NULL) {
    sendstr("Connection identifier not in use.\n", com->conn);
    return ESUCCESS;
  }

  buf = netconn_recv(conns[i]);
  if (buf != NULL) {
      
    netbuf_copy(buf, buffer, 1024);
    len = netbuf_len(buf);
    sendstr("Reading from connection:\n", com->conn);
    netconn_write(com->conn, buffer, len, NETCONN_COPY);
    netbuf_delete(buf);
  } else {
    sendstr("EOF.\n", com->conn); 
  }
  err = netconn_err(conns[i]);
  if (err != ERR_OK) {
    sendstr("Could not receive data: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(err), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    return ESUCCESS;
  }
  return ESUCCESS;
}
/*-----------------------------------------------------------------------------------*/
static s8_t
com_udpc(struct command *com)
{
  struct ip_addr ipaddr;
  u16_t lport, rport;
  int i;
  err_t err;

  lport = strtol(com->args[0], NULL, 10);
  if (inet_aton(com->args[1], (struct in_addr *)&ipaddr) == -1) {
    sendstr(strerror(errno), com->conn);
    return ESYNTAX;
  }
  rport = strtol(com->args[2], NULL, 10);

  /* Find the first unused connection in conns. */
  for(i = 0; i < NCONNS && conns[i] != NULL; i++);

  if (i == NCONNS) {
    sendstr("No more connections available, sorry.\n", com->conn);
    return ESUCCESS;
  }

  sendstr("Setting up UDP connection from port ", com->conn);
  netconn_write(com->conn, com->args[0], strlen(com->args[0]), NETCONN_COPY);
  sendstr(" to ", com->conn);
  netconn_write(com->conn, com->args[1], strlen(com->args[1]), NETCONN_COPY);
  sendstr(":", com->conn);
  netconn_write(com->conn, com->args[2], strlen(com->args[2]), NETCONN_COPY);
  sendstr("\n", com->conn);

  conns[i] = netconn_new(NETCONN_UDP);
  if (conns[i] == NULL) {    
    sendstr("Could not create connection identifier (out of memory).\n", com->conn); 
    return ESUCCESS;
  }

  err = netconn_connect(conns[i], &ipaddr, rport);
  if (err != ERR_OK) {
    netconn_delete(conns[i]);
    conns[i] = NULL;
    sendstr("Could not connect to remote host: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(err), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    return ESUCCESS;
  }

  err = netconn_bind(conns[i], IP_ADDR_ANY, lport);
  if (err != ERR_OK) {
    netconn_delete(conns[i]);
    conns[i] = NULL;
    sendstr("Could not bind: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(err), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    return ESUCCESS;
  }

  sendstr("Connection set up, connection identifier is ", com->conn);
  snprintf((char *)buffer, sizeof(buffer), "%d\n", i);
  netconn_write(com->conn, buffer, strlen((const char *)buffer), NETCONN_COPY);
  
  return ESUCCESS;
}
/*-----------------------------------------------------------------------------------*/
static s8_t
com_udpl(struct command *com)
{
  struct ip_addr ipaddr;
  u16_t lport, rport;
  int i;
  err_t err;

  lport = strtol(com->args[0], NULL, 10);
  if (inet_aton(com->args[1], (struct in_addr *)&ipaddr) == -1) {
    sendstr(strerror(errno), com->conn);
    return ESYNTAX;
  }
  rport = strtol(com->args[2], NULL, 10);

  /* Find the first unused connection in conns. */
  for(i = 0; i < NCONNS && conns[i] != NULL; i++);

  if (i == NCONNS) {
    sendstr("No more connections available, sorry.\n", com->conn);
    return ESUCCESS;
  }

  sendstr("Setting up UDP-Lite connection from port ", com->conn);
  netconn_write(com->conn, com->args[0], strlen(com->args[0]), NETCONN_COPY);
  sendstr(" to ", com->conn);
  netconn_write(com->conn, com->args[1], strlen(com->args[1]), NETCONN_COPY);
  sendstr(":", com->conn);
  netconn_write(com->conn, com->args[2], strlen(com->args[2]), NETCONN_COPY);
  sendstr("\n", com->conn);

  conns[i] = netconn_new(NETCONN_UDPLITE);
  if (conns[i] == NULL) {    
    sendstr("Could not create connection identifier (out of memory).\n", com->conn); 
    return ESUCCESS;
  }

  err = netconn_connect(conns[i], &ipaddr, rport);
  if (err != ERR_OK) {
    netconn_delete(conns[i]);
    conns[i] = NULL;
    sendstr("Could not connect to remote host: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(err), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    return ESUCCESS;
  }

  err = netconn_bind(conns[i], IP_ADDR_ANY, lport);
  if (err != ERR_OK) {
    netconn_delete(conns[i]);
    conns[i] = NULL;
    sendstr("Could not bind: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(err), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    return ESUCCESS;
  }

  sendstr("Connection set up, connection identifier is ", com->conn);
  snprintf((char *)buffer, sizeof(buffer), "%d\n", i);
  netconn_write(com->conn, buffer, strlen((const char *)buffer), NETCONN_COPY);
  
  return ESUCCESS;
}
/*-----------------------------------------------------------------------------------*/
static s8_t
com_udpn(struct command *com)
{
  struct ip_addr ipaddr;
  u16_t lport, rport;
  int i;
  err_t err;

  lport = strtol(com->args[0], NULL, 10);
  if (inet_aton(com->args[1], (struct in_addr *)&ipaddr) == -1) {
    sendstr(strerror(errno), com->conn);
    return ESYNTAX;
  }
  rport = strtol(com->args[2], NULL, 10);

  /* Find the first unused connection in conns. */
  for(i = 0; i < NCONNS && conns[i] != NULL; i++);

  if (i == NCONNS) {
    sendstr("No more connections available, sorry.\n", com->conn);
    return ESUCCESS;
  }

  sendstr("Setting up UDP connection without checksums from port ", com->conn);
  netconn_write(com->conn, com->args[0], strlen(com->args[0]), NETCONN_COPY);
  sendstr(" to ", com->conn);
  netconn_write(com->conn, com->args[1], strlen(com->args[1]), NETCONN_COPY);
  sendstr(":", com->conn);
  netconn_write(com->conn, com->args[2], strlen(com->args[2]), NETCONN_COPY);
  sendstr("\n", com->conn);

  conns[i] = netconn_new(NETCONN_UDPNOCHKSUM);
  if (conns[i] == NULL) {    
    sendstr("Could not create connection identifier (out of memory).\n", com->conn); 
    return ESUCCESS;
  }

  err = netconn_connect(conns[i], &ipaddr, rport);
  if (err != ERR_OK) {
    netconn_delete(conns[i]);
    conns[i] = NULL;
    sendstr("Could not connect to remote host: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(err), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    return ESUCCESS;
  }

  err = netconn_bind(conns[i], IP_ADDR_ANY, lport);
  if (err != ERR_OK) {
    netconn_delete(conns[i]);
    conns[i] = NULL;
    sendstr("Could not bind: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(err), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    return ESUCCESS;
  }

  sendstr("Connection set up, connection identifier is ", com->conn);
  snprintf((char *)buffer, sizeof(buffer), "%d\n", i);
  netconn_write(com->conn, buffer, strlen((const char *)buffer), NETCONN_COPY);
  
  return ESUCCESS;
}
/*-----------------------------------------------------------------------------------*/
static s8_t
com_udpb(struct command *com)
{
  struct ip_addr ipaddr;
  u16_t lport, rport;
  int i;
  err_t err;
  struct ip_addr bcaddr;

  lport = strtol(com->args[0], NULL, 10);
  if (inet_aton(com->args[1], (struct in_addr *)&ipaddr) == -1) {
    sendstr(strerror(errno), com->conn);
    return ESYNTAX;
  }
  rport = strtol(com->args[2], NULL, 10);

  /* Find the first unused connection in conns. */
  for(i = 0; i < NCONNS && conns[i] != NULL; i++);

  if (i == NCONNS) {
    sendstr("No more connections available, sorry.\n", com->conn);
    return ESUCCESS;
  }

  sendstr("Setting up UDP broadcast connection from port ", com->conn);
  netconn_write(com->conn, com->args[0], strlen(com->args[0]), NETCONN_COPY);
  sendstr(" to ", com->conn);
  netconn_write(com->conn, com->args[1], strlen(com->args[1]), NETCONN_COPY);
  sendstr("\n", com->conn);

  conns[i] = netconn_new(NETCONN_UDP);
  if (conns[i] == NULL) {    
    sendstr("Could not create connection identifier (out of memory).\n", com->conn); 
    return ESUCCESS;
  }

  err = netconn_connect(conns[i], &ipaddr, rport);
  if (err != ERR_OK) {
    netconn_delete(conns[i]);
    conns[i] = NULL;
    sendstr("Could not connect to remote host: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(err), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    return ESUCCESS;
  }

  IP4_ADDR(&bcaddr, 255,255,255,255);
  err = netconn_bind(conns[i], &bcaddr, lport);
  if (err != ERR_OK) {
    netconn_delete(conns[i]);
    conns[i] = NULL;
    sendstr("Could not bind: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(err), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    return ESUCCESS;
  }

  sendstr("Connection set up, connection identifier is ", com->conn);
  snprintf((char *)buffer, sizeof(buffer), "%d\n", i);
  netconn_write(com->conn, buffer, strlen((const char *)buffer), NETCONN_COPY);
  
  return ESUCCESS;
}
/*-----------------------------------------------------------------------------------*/
static s8_t
com_usnd(struct command *com)
{
  int i;
  err_t err;
  struct netbuf *buf;
  char *mem;
  
  i = strtol(com->args[0], NULL, 10);

  if (i > NCONNS) {
    sendstr("Connection identifier too high.\n", com->conn);
    return ESUCCESS;
  }

  if (conns[i] == NULL) {
    sendstr("Connection identifier not in use.\n", com->conn);
    return ESUCCESS;
  }

  buf = netbuf_new();
  mem = netbuf_alloc(buf, strlen(com->args[1]) + 1);
  if (mem == NULL) {
    sendstr("Could not allocate memory for sending.\n", com->conn);
    return ESUCCESS;
  }
  strncpy(mem, com->args[1], strlen(com->args[1]) + 1);
  err = netconn_send(conns[i], buf);
  netbuf_delete(buf);
  if (err != ERR_OK) {
    sendstr("Could not send data: ", com->conn);
#ifdef LWIP_DEBUG
    sendstr(lwip_strerr(err), com->conn);
#else
    sendstr("(debugging must be turned on for error message to appear)", com->conn);
#endif /* LWIP_DEBUG */
    sendstr("\n", com->conn);
    return ESUCCESS;
  }
  
  sendstr("Data sent.\n", com->conn);
  return ESUCCESS;
}
/*-----------------------------------------------------------------------------------*/
static s8_t
com_help(struct command *com)
{
  sendstr(help_msg, com->conn);
  return ESUCCESS;
}
/*-----------------------------------------------------------------------------------*/
static s8_t
parse_command(struct command *com, u32_t len)
{
  u16_t i;
  u16_t bufp;
  
  if (strncmp((const char *)buffer, "open", 4) == 0) {
    com->exec = com_open;
    com->nargs = 2;
  } else if (strncmp((const char *)buffer, "lstn", 4) == 0) {
    com->exec = com_lstn;
    com->nargs = 1;
  } else if (strncmp((const char *)buffer, "acpt", 4) == 0) {
    com->exec = com_acpt;
    com->nargs = 1;
  } else if (strncmp((const char *)buffer, "clos", 4) == 0) {
    com->exec = com_clos;
    com->nargs = 1;
#if LWIP_STATS    
  } else if (strncmp((const char *)buffer, "stat", 4) == 0) {
    com->exec = com_stat;
    com->nargs = 0;
#endif    
  } else if (strncmp((const char *)buffer, "send", 4) == 0) {
    com->exec = com_send;
    com->nargs = 2;
  } else if (strncmp((const char *)buffer, "recv", 4) == 0) {
    com->exec = com_recv;
    com->nargs = 1;
  } else if (strncmp((const char *)buffer, "udpc", 4) == 0) {
    com->exec = com_udpc;
    com->nargs = 3;
  } else if (strncmp((const char *)buffer, "udpb", 4) == 0) {
    com->exec = com_udpb;
    com->nargs = 2;
  } else if (strncmp((const char *)buffer, "udpl", 4) == 0) {
    com->exec = com_udpl;
    com->nargs = 3;
  } else if (strncmp((const char *)buffer, "udpn", 4) == 0) {
    com->exec = com_udpn;
    com->nargs = 3;
  } else if (strncmp((const char *)buffer, "usnd", 4) == 0) {
    com->exec = com_usnd;
    com->nargs = 2;
  } else if (strncmp((const char *)buffer, "help", 4) == 0) {
    com->exec = com_help;
    com->nargs = 0;
  } else if (strncmp((const char *)buffer, "quit", 4) == 0) {
    printf("quit\n");
    return ECLOSED;
  } else {
    return ESYNTAX;
  }

  if (com->nargs == 0) {
    return ESUCCESS;
  }
  bufp = 0;
  for(; bufp < len && buffer[bufp] != ' '; bufp++);
  for(i = 0; i < 10; i++) {
    for(; bufp < len && buffer[bufp] == ' '; bufp++);
    if (buffer[bufp] == '\r' ||
       buffer[bufp] == '\n') {
      buffer[bufp] = 0;
      if (i < com->nargs - 1) {
	return ETOOFEW;
      }
      if (i > com->nargs - 1) {
	return ETOOMANY;
      }
      break;
    }    
    if (bufp > len) {
      return ETOOFEW;
    }    
    com->args[i] = (char *)&buffer[bufp];
    for(; bufp < len && buffer[bufp] != ' ' && buffer[bufp] != '\r' &&
	  buffer[bufp] != '\n'; bufp++) {
      if (buffer[bufp] == '\\') {
	buffer[bufp] = ' ';
      }
    }
    if (bufp > len) {
      return ESYNTAX;
    }
    buffer[bufp] = 0;
    bufp++;
    if (i == com->nargs - 1) {
      break;
    }

  }

  return ESUCCESS;
}
/*-----------------------------------------------------------------------------------*/
static void
error(s8_t err, struct netconn *conn)
{
  switch (err) {
  case ESYNTAX:
    sendstr("## Syntax error\n", conn);
    break;
  case ETOOFEW:
    sendstr("## Too few arguments to command given\n", conn);
    break;
  case ETOOMANY:
    sendstr("## Too many arguments to command given\n", conn);
    break;
  }
}
/*-----------------------------------------------------------------------------------*/
static void
prompt(struct netconn *conn)
{
  sendstr("> ", conn);
}  
/*-----------------------------------------------------------------------------------*/
static void
shell_main(struct netconn *conn)
{
  struct netbuf *buf;
  u32_t len;
  struct command com;
  s8_t err;
  int i;
  
  do {
    buf = netconn_recv(conn);
    if (buf != NULL) {
      netbuf_copy(buf, buffer, 1024);
      len = netbuf_len(buf);
      netbuf_delete(buf);
      if (len >= 4) {
	if (buffer[0] != 0xff && 
	   buffer[1] != 0xfe) {
	  err = parse_command(&com, len);
	  if (err == ESUCCESS) {	
	    com.conn = conn;
	    err = com.exec(&com);
	  }
	  if (err != ESUCCESS) {
	    error(err, conn);
	  }
	  if (err == ECLOSED) {
	    printf("Closed\n");
	    error(err, conn);
	    goto close;
	  }
	} else {
	  sendstr("\n\n"
	          "lwIP simple interactive shell.\n"
	          "(c) Copyright 2001, Swedish Institute of Computer Science.\n"
	          "Written by Adam Dunkels.\n"
	          "For help, try the \"help\" command.\n", conn);
	}
      }
    }
    if (buf != NULL) {
      prompt(conn);
    }
  } while (buf != NULL);
  printf("buf == NULL err %s\n", lwip_strerr(conn->err));
 close:  
  netconn_close(conn);
  
  for(i = 0; i < NCONNS; i++) {
    if (conns[i] != NULL) {
      netconn_delete(conns[i]);
    }
    conns[i] = NULL;
  }
  
}
/*-----------------------------------------------------------------------------------*/
static void 
shell_thread(void *arg)
{
  struct netconn *conn, *newconn;
  
  conn = netconn_new(NETCONN_TCP);
  netconn_bind(conn, NULL, 23);
  netconn_listen(conn);

  while (1) {
    newconn = netconn_accept(conn);
    shell_main(newconn);
    netconn_delete(newconn);
  }
}
/*-----------------------------------------------------------------------------------*/
void
shell_init(void)     
{
  sys_thread_new("shell_thread", shell_thread, NULL, DEFAULT_THREAD_STACKSIZE, DEFAULT_THREAD_PRIO);
}




