/****************************************************************************
 *                            IPSTACK COMPONENTS                            *
 *          Copyright (C) 2010-2012, Free Software Foundation, Inc.         *
 ****************************************************************************/

/* C binding to AIP library */

/* These declarations must be kept in synch with the corrsponding Ada ones. */

#ifndef __AIP_H__
#define __AIP_H__

/*******
 * AIP *
 *******/

typedef unsigned char   U8_T;
typedef signed short    S16_T;
typedef unsigned short  U16_T;
typedef unsigned int    U32_T;
typedef void           *IPTR_T;
typedef signed int      EID;
typedef char            Ethernet_Address[6];

typedef unsigned char   Err_T;
#define NOERR    0
#define ERR_MEM -1

/***************
 * AIP.Buffers *
 ***************/

typedef enum { SPLIT_BUF, LINK_BUF, REF_BUF } Buffer_Kind;
typedef U16_T Buffer_Length;
typedef U16_T Data_Length;

typedef U16_T Buffer_Id;
#define NOBUF 0

extern void
AIP_buffer_alloc
  (Buffer_Length Offset,
   Data_Length   Size,
   Buffer_Kind   Kind,
   Buffer_Id    *Buf);

extern void
AIP_buffer_ref (Buffer_Id Buf);

extern U16_T
AIP_buffer_len (Buffer_Id Buf);

extern U16_T
AIP_buffer_tlen (Buffer_Id Buf);

extern void
AIP_buffer_set_payload_len (Buffer_Id Buf, U16_T Len, Err_T *Err);

extern Buffer_Id
AIP_buffer_next (Buffer_Id Buf);

extern IPTR_T
AIP_buffer_payload (Buffer_Id Buf);

extern void
AIP_buffer_header (Buffer_Id Buf, S16_T Bump, Err_T *Err);

extern void
AIP_buffer_cat (Buffer_Id Head, Buffer_Id Tail);

extern void
AIP_buffer_blind_free (Buffer_Id Buf);

/***************
 * AIP.IPaddrs *
 ***************/

typedef U32_T IPaddr;

/***********
 * AIP.NIF *
 ***********/

typedef enum { Invalid, Down, Up } Netif_State;

typedef EID Netif_Id;
#define IF_NOID (-1)

typedef enum { IP_CS, ICMP_CS, UDP_CS, TCP_CS } Checsum_Type;

#define MAX_LL_ADDRESS_LENGTH 6

typedef struct netif {
  char        Name[2];
  Netif_State State;

  char        LL_Address[MAX_LL_ADDRESS_LENGTH];
  U8_T        LL_Address_Length;

  U16_T       MTU;

  IPaddr      IP;
  IPaddr      Mask;
  IPaddr      Broadcast;
  IPaddr      Remote;

  char        Offload[4];

  void      (*Configured_CB) (Netif_Id, Err_T *);
  void      (*Input_CB) (Netif_Id, Buffer_Id);
  void      (*Output_CB) (Netif_Id, Buffer_Id, IPaddr);
  void      (*Link_Output_CB) (Netif_Id, Buffer_Id, Err_T *);

  IPTR_T Dev;
} Netif;

extern struct netif *
AIP_get_netif (EID Nid);

/***********
 * AIP.ARP *
 ***********/

extern void
AIP_arp_input (Netif_Id Nid, IPTR_T Netif_Address, Buffer_Id Buf);

extern void
AIP_arpip_input (Netif_Id Nid, Buffer_Id Buf);

extern void
AIP_arp_output (Netif_Id Nid, Buffer_Id Buf, IPaddr Dst_Address);

/**********
 * AIP.IP *
 **********/

extern void
AIP_ip_input (Netif_Id Nid, Buffer_Id Buf);

/**************
 * AIP.EtherH *
 **************/

#include "etherh.h"

/***********************
 * Compatibility shims *
 ***********************/

#define err_t Err_T

#endif /* __AIP_H__ */
