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
 * RT timer modifications by Christiaan Simons
 */

#include "lwip/init.h"

#include "lwip/debug.h"

#include "lwip/mem.h"
#include "lwip/memp.h"
#include "lwip/sys.h"

#include "lwip/stats.h"

#include "lwip/ip.h"
#include "lwip/ip_frag.h"
#include "lwip/udp.h"
#include "lwip/tcp.h"
#include "ne2kif.h"
#include "netif/etharp.h"

#include "timer.h"

/* (manual) host IP configuration */
static struct ip_addr ipaddr, netmask, gw;

/* SNMP trap destination cmd option */
static unsigned char trap_flag;

/* nonstatic debug cmd option, exported in lwipopts.h */
unsigned char debug_flags;

/* 'non-volatile' SNMP settings
  @todo: make these truly non-volatile */
u8_t syscontact_str[255];
u8_t syscontact_len = 0;
u8_t syslocation_str[255];
u8_t syslocation_len = 0;

static struct netif netif;

void
C_init (void)
{
  struct in_addr inaddr;
  char ip_str[16] = {0}, nm_str[16] = {0}, gw_str[16] = {0};

  /* startup defaults (may be overridden by one or more opts) */
  IP4_ADDR(&gw, 192,168,0,1);
  IP4_ADDR(&ipaddr, 192,168,0,2);
  IP4_ADDR(&netmask, 255,255,255,0);

  trap_flag = 0;
  /* use debug flags defined by debug.h */
  debug_flags = LWIP_DBG_OFF;

  inaddr.s_addr = ipaddr.addr;
  strncpy(ip_str,inet_ntoa(inaddr),sizeof(ip_str));
  inaddr.s_addr = netmask.addr;
  strncpy(nm_str,inet_ntoa(inaddr),sizeof(nm_str));
  inaddr.s_addr = gw.addr;
  strncpy(gw_str,inet_ntoa(inaddr),sizeof(gw_str));

  printf("Host at %s mask %s gateway %s\n", ip_str, nm_str, gw_str);
        
  lwip_init();

  printf("TCP/IP initialized.\n");
  
  netif_add(&netif, &ipaddr, &netmask, &gw, NULL, ne2k_init, ip_input);  
  netif_set_default(&netif);
  netif_set_up(&netif);

  timer_init();
  timer_set_interval(TIMER_EVT_ETHARPTMR,2000);
  timer_set_interval(TIMER_EVT_TCPFASTTMR, TCP_FAST_INTERVAL / 10);
  timer_set_interval(TIMER_EVT_TCPSLOWTMR, TCP_SLOW_INTERVAL / 10);
  
  printf("Applications started.\n");

  return;
}
