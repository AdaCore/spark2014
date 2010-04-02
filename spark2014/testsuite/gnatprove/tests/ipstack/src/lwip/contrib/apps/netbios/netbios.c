/**
 * @file
 * NetBIOS name service sample
 *
 */

/*
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
 */

#include "lwip/opt.h"

#if LWIP_UDP  /* don't build if not configured for use in lwipopts.h */

#include "lwip/udp.h"
#include "lwip/netif.h"

/** This is an example implementation of a NetBIOS name server.
 * It responds to name queries for a configurable name.
 * Name resolving is not supported.
 *
 * Note that the device doesn't broadcast it's own name so can't
 * detect duplicate names!
 */

/** NetBIOS name of LWIP device */
#ifndef NETBIOS_LWIP_NAME
#define NETBIOS_LWIP_NAME "NETBIOSLWIPDEV"
#endif

/** default port number for "NetBIOS Name service */
#define NETBIOS_PORT     137

/** size of a NetBIOS name */
#define NETBIOS_NAME_LEN 16

/** The Time-To-Live for NetBIOS name responds (in seconds)
 * Default is 300000 seconds (3 days, 11 hours, 20 minutes) */
#define NETBIOS_NAME_TTL 300000

/** NetBIOS header flags */
#define NETB_HFLAG_RESPONSE           0x8000
#define NETB_HFLAG_OPCODE             0x7800
#define NETB_HFLAG_OPCODE_NAME_QUERY  0x0000
#define NETB_HFLAG_AUTHORATIVE        0x0400
#define NETB_HFLAG_TRUNCATED          0x0200
#define NETB_HFLAG_RECURS_DESIRED     0x0100
#define NETB_HFLAG_RECURS_AVAILABLE   0x0080
#define NETB_HFLAG_BROADCAST          0x0010
#define NETB_HFLAG_REPLYCODE          0x0008
#define NETB_HFLAG_REPLYCODE_NOERROR  0x0000

/** NetBIOS name flags */
#define NETB_NFLAG_UNIQUE             0x8000
#define NETB_NFLAG_NODETYPE           0x6000
#define NETB_NFLAG_NODETYPE_HNODE     0x6000
#define NETB_NFLAG_NODETYPE_MNODE     0x4000
#define NETB_NFLAG_NODETYPE_PNODE     0x2000
#define NETB_NFLAG_NODETYPE_BNODE     0x0000

/** NetBIOS message header */
#ifdef PACK_STRUCT_USE_INCLUDES
#  include "arch/bpstruct.h"
#endif
PACK_STRUCT_BEGIN
struct netbios_hdr {
  PACK_STRUCT_FIELD(u16_t trans_id);
  PACK_STRUCT_FIELD(u16_t flags);
  PACK_STRUCT_FIELD(u16_t questions);
  PACK_STRUCT_FIELD(u16_t answerRRs);
  PACK_STRUCT_FIELD(u16_t authorityRRs);
  PACK_STRUCT_FIELD(u16_t additionalRRs);
} PACK_STRUCT_STRUCT;
PACK_STRUCT_END
#ifdef PACK_STRUCT_USE_INCLUDES
#  include "arch/epstruct.h"
#endif

/** NetBIOS message name part */
#ifdef PACK_STRUCT_USE_INCLUDES
#  include "arch/bpstruct.h"
#endif
PACK_STRUCT_BEGIN
struct netbios_name_hdr {
  PACK_STRUCT_FIELD(u8_t  nametype);
  PACK_STRUCT_FIELD(u8_t  encname[(NETBIOS_NAME_LEN*2)+1]);
  PACK_STRUCT_FIELD(u16_t type);
  PACK_STRUCT_FIELD(u16_t class);
  PACK_STRUCT_FIELD(u32_t ttl);
  PACK_STRUCT_FIELD(u16_t datalen);
  PACK_STRUCT_FIELD(u16_t flags);
  PACK_STRUCT_FIELD(u32_t addr);
} PACK_STRUCT_STRUCT;
PACK_STRUCT_END
#ifdef PACK_STRUCT_USE_INCLUDES
#  include "arch/epstruct.h"
#endif

/** NetBIOS message */
#ifdef PACK_STRUCT_USE_INCLUDES
#  include "arch/bpstruct.h"
#endif
PACK_STRUCT_BEGIN
struct netbios_resp
{
  struct netbios_hdr      resp_hdr;
  struct netbios_name_hdr resp_name;
} PACK_STRUCT_STRUCT;
PACK_STRUCT_END
#ifdef PACK_STRUCT_USE_INCLUDES
#  include "arch/epstruct.h"
#endif

/** NetBIOS decoding name */
static int
netbios_name_decoding( char *name_enc, char *name_dec, int name_dec_len)
{
  char *pname;
  char  cname;
  char  cnbname;
  int   index = 0;

  LWIP_UNUSED_ARG(name_dec_len);

  /* Start decoding netbios name. */
  pname  = name_enc;
  for (;;) {
    /* Every two characters of the first level-encoded name
     * turn into one character in the decoded name. */
    cname = *pname;
    if (cname == '\0')
      break;    /* no more characters */
    if (cname == '.')
      break;    /* scope ID follows */
    if (cname < 'A' || cname > 'Z') {
      /* Not legal. */
      return -1;
    }
    cname -= 'A';
    cnbname = cname << 4;
    pname++;

    cname = *pname;
    if (cname == '\0' || cname == '.') {
      /* No more characters in the name - but we're in
       * the middle of a pair.  Not legal. */
      return -1;
    }
    if (cname < 'A' || cname > 'Z') {
      /* Not legal. */
      return -1;
    }
    cname -= 'A';
    cnbname |= cname;
    pname++;

    /* Do we have room to store the character? */
    if (index < NETBIOS_NAME_LEN) {
      /* Yes - store the character. */
      name_dec[index++] = (cnbname!=' '?cnbname:'\0');
    }
  }

  return 0;
}

/** NetBIOS encoding name */
static int
netbios_name_encoding(char *name_enc, char *name_dec, int name_dec_len)
{
  char         *pname;
  char          cname;
  unsigned char ucname;
  int           index = 0;
  
  /* Start encoding netbios name. */
  pname = name_enc;

  for (;;) {
    /* Every two characters of the first level-encoded name
     * turn into one character in the decoded name. */
    cname = *pname;
    if (cname == '\0')
      break;    /* no more characters */
    if (cname == '.')
      break;    /* scope ID follows */
    if ((cname < 'A' || cname > 'Z') && (cname < '0' || cname > '9')) {
      /* Not legal. */
      return -1;
    }

    /* Do we have room to store the character? */
    if (index >= name_dec_len) {
      return -1;
    }

    /* Yes - store the character. */
    ucname = cname;
    name_dec[index++] = ('A'+((ucname>>4) & 0x0F));
    name_dec[index++] = ('A'+( ucname     & 0x0F));
    pname++;
  }

  /* Fill with "space" coding */
  for (;index<name_dec_len-1;) {
    name_dec[index++] = 'C';
    name_dec[index++] = 'A';
  }

  /* Terminate string */
  name_dec[index]='\0';

  return 0;
}

/** NetBIOS Name service recv callback */
static void
netbios_recv(void *arg, struct udp_pcb *upcb, struct pbuf *p, struct ip_addr *addr, u16_t port)
{
  LWIP_UNUSED_ARG(arg);

  /* if packet is valid */
  if (p != NULL) {
    char   netbios_name[NETBIOS_NAME_LEN+1];
    struct netbios_hdr*      netbios_hdr      = p->payload;
    struct netbios_name_hdr* netbios_name_hdr = (struct netbios_name_hdr*)(netbios_hdr+1);
    
    /* we only answer if we got a default interface */
    if (netif_default != NULL) {
      /* @todo: do we need to check answerRRs/authorityRRs/additionalRRs? */
      /* if the packet is a NetBIOS name query question */
      if (((ntohs(netbios_hdr->flags) & NETB_HFLAG_OPCODE) == NETB_HFLAG_OPCODE_NAME_QUERY) &&
          ((ntohs(netbios_hdr->flags) & NETB_HFLAG_RESPONSE) == 0) &&
           (ntohs(netbios_hdr->questions) == 1)) {
        /* decode the NetBIOS name */
        netbios_name_decoding( (char*)(netbios_name_hdr->encname), netbios_name, sizeof(netbios_name));
        /* if the packet is for us */
        if (strcmp( netbios_name, NETBIOS_LWIP_NAME)==0) {
          struct pbuf *q;
          struct netbios_resp *resp;

          q = pbuf_alloc(PBUF_TRANSPORT, sizeof(struct netbios_resp), PBUF_RAM);
          if (q != NULL) {
            resp = (struct netbios_resp*)q->payload;

            /* prepare NetBIOS header response */
            resp->resp_hdr.trans_id      = netbios_hdr->trans_id;
            resp->resp_hdr.flags         = htons(NETB_HFLAG_RESPONSE |
                                                 NETB_HFLAG_OPCODE_NAME_QUERY |
                                                 NETB_HFLAG_AUTHORATIVE |
                                                 NETB_HFLAG_RECURS_DESIRED);
            resp->resp_hdr.questions     = 0;
            resp->resp_hdr.answerRRs     = htons(1);
            resp->resp_hdr.authorityRRs  = 0;
            resp->resp_hdr.additionalRRs = 0;

            /* prepare NetBIOS header datas */
            MEMCPY( resp->resp_name.encname, netbios_name_hdr->encname, sizeof(netbios_name_hdr->encname));
            resp->resp_name.nametype     = netbios_name_hdr->nametype;
            resp->resp_name.type         = netbios_name_hdr->type;
            resp->resp_name.class        = netbios_name_hdr->class;
            resp->resp_name.ttl          = htonl(NETBIOS_NAME_TTL);
            resp->resp_name.datalen      = htons(sizeof(resp->resp_name.flags)+sizeof(resp->resp_name.addr));
            resp->resp_name.flags        = htons(NETB_NFLAG_NODETYPE_BNODE);
            resp->resp_name.addr         = netif_default->ip_addr.addr;

            /* send the NetBIOS response */
            udp_sendto(upcb, q, addr, port);
            
            /* free the "reference" pbuf */
            pbuf_free(q);
          }
        }
      }
    }
    /* free the pbuf */
    pbuf_free(p);
  }
}

void netbios_init(void)
{
  struct udp_pcb *pcb;

  LWIP_ASSERT("NetBIOS name is too long!", strlen(NETBIOS_LWIP_NAME) < NETBIOS_NAME_LEN);

  pcb = udp_new();
  if (pcb != NULL) {
    udp_bind(pcb, IP_ADDR_ANY, NETBIOS_PORT);
    udp_recv(pcb, netbios_recv, pcb);
  }
}
#endif /* LWIP_UDP */
