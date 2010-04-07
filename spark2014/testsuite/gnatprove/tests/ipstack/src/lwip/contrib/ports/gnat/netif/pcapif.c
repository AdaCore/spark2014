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

#ifndef linux  /* Apparently, this doesn't work under Linux. */

#include "lwip/debug.h"

#include <fcntl.h>
#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/uio.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <sys/stat.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#include <pcap.h>

#include "netif/etharp.h"

#include "lwip/stats.h"

#include "lwip/def.h"
#include "lwip/mem.h"
#include "lwip/pbuf.h"
#include "netif/unixif.h"
#include "lwip/sys.h"

#include "lwip/ip.h"


#if defined(LWIP_DEBUG) && defined(LWIP_TCPDUMP)
#include "netif/tcpdump.h"
#endif /* LWIP_DEBUG && LWIP_TCPDUMP */

struct pcapif {
  pcap_t *pd;
  sys_sem_t sem;
  u8_t pkt[2048];
  u32_t len;
  u32_t lasttime;
  struct pbuf *p;
  struct eth_addr *ethaddr;
};

static char errbuf[PCAP_ERRBUF_SIZE];

/*-----------------------------------------------------------------------------------*/
static err_t
pcapif_output(struct netif *netif, struct pbuf *p,
	      struct ip_addr *ipaddr)
{
  return ERR_OK;
}
/*-----------------------------------------------------------------------------------*/
static void
timeout(void *arg)
{
  struct netif *netif;
  struct pcapif *pcapif;
  struct pbuf *p, *q;
  u8_t *bufptr;
  struct eth_hdr *ethhdr;
  
  netif = (struct netif *)arg;
  pcapif = netif->state;
  ethhdr = (struct eth_hdr *)pcapif->pkt;

  
  if (htons(ethhdr->type) != ETHTYPE_IP ||
     ip_lookup(pcapif->pkt + 14, netif)) {
    
    /* We allocate a pbuf chain of pbufs from the pool. */
    p = pbuf_alloc(PBUF_LINK, pcapif->len, PBUF_POOL);
    
    if (p != NULL) {
      /* We iterate over the pbuf chain until we have read the entire
	 packet into the pbuf. */
      bufptr = (u_char *)pcapif->pkt;
      for(q = p; q != NULL; q = q->next) {
	/* Read enough bytes to fill this pbuf in the chain. The
	   available data in the pbuf is given by the q->len
	   variable. */
	/* read data into(q->payload, q->len); */
	bcopy(bufptr, q->payload, q->len);
	bufptr += q->len;
      }

#if defined(LWIP_DEBUG) && defined(LWIP_TCPDUMP)
      tcpdump(p);
#endif /* LWIP_DEBUG && LWIP_TCPDUMP */

      ethhdr = p->payload;
      switch (htons(ethhdr->type)) {
      case ETHTYPE_IP:
	etharp_ip_input(netif, p);
	pbuf_header(p, -14);
	netif->input(p, netif);
	break;
      case ETHTYPE_ARP:
	    etharp_arp_input(netif, pcapif->ethaddr, p);
     	break;
  default:
	    pbuf_free(p);
     	break;
      }
    }
  } else {
    printf("ip_lookup dropped\n");
  }

  sys_sem_signal(pcapif->sem);
}
/*-----------------------------------------------------------------------------------*/
static void
callback(u_char *arg, const struct pcap_pkthdr *hdr, const u_char *pkt)
{
  struct netif *netif;
  struct pcapif *pcapif;
  u32_t time, lasttime;
  
  netif = (struct netif *)arg;
  pcapif = netif->state;

  pcapif->len = hdr->len;
  
  bcopy(pkt, pcapif->pkt, hdr->len);

  time = hdr->ts.tv_sec * 1000 + hdr->ts.tv_usec / 1000;

  lasttime = pcapif->lasttime;
  pcapif->lasttime = time;
  

  if (lasttime == 0) {
    sys_timeout(1000, timeout, netif);
  } else {
    sys_timeout(time - lasttime, timeout, netif);
  }
}
/*-----------------------------------------------------------------------------------*/
static void
pcapif_thread(void *arg)
{
  struct netif *netif;
  struct pcapif *pcapif;
  netif = arg;
  pcapif = netif->state;

  while (1) {
    pcap_loop(pcapif->pd, 1, callback, (u_char *)netif);
    sys_sem_wait(pcapif->sem);
    if (pcapif->p != NULL) {
      netif->input(pcapif->p, netif);
    }
  }
}
/*-----------------------------------------------------------------------------------*/
err_t
pcapif_init(struct netif *netif)
{
  struct pcapif *p;
    
  p = malloc(sizeof(struct pcapif));
  if (p == NULL)
      return ERR_MEM;
  netif->state = p;
  netif->name[0] = 'p';
  netif->name[1] = 'c';
  netif->output = pcapif_output;

  p->pd = pcap_open_offline("pcapdump", errbuf);
  if (p->pd == NULL) {
    printf("pcapif_init: failed %s\n", errbuf);
    return ERR_IF;
  }

  p->sem = sys_sem_new(0);
  p->p = NULL;
  p->lasttime = 0; 
  
  sys_thread_new("pcapif_thread", pcapif_thread, netif, DEFAULT_THREAD_STACKSIZE, DEFAULT_THREAD_PRIO);
  return ERR_OK;
}
/*-----------------------------------------------------------------------------------*/
#endif /* linux */
