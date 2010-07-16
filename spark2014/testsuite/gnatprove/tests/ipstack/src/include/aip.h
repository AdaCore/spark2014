/****************************************************************************
 *                            IPSTACK COMPONENTS                            *
 *             Copyright (C) 2010, Free Software Foundation, Inc.           *
 ****************************************************************************/

/* C binding to AIP library */

/* These declarations must be kept in synch with the corrsponding Ada ones. */

#ifndef __AIP_H__
#define __AIP_H__

/*******
 * AIP *
 *******/

typedef unsigned char   U8_T;
typedef unsigned short  U16_T;
typedef unsigned int    U32_T;
typedef unsigned long   M32_T;
typedef void           *IPTR_T;
typedef signed int      EID;
typedef char            Ethernet_Address[6];

typedef unsigned char   Err_T;
#define NOERR    0
#define ERR_MEM -1

/***************
 * AIP.Buffers *
 ***************/

typedef enum { MONO_BUF, LINK_BUF, REF_BUF } Buffer_Kind;
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

extern U16_T
AIP_buffer_len (Buffer_Id Buf);

extern U16_T
AIP_buffer_tlen (Buffer_Id Buf);

extern Buffer_Id
AIP_buffer_next (Buffer_Id Buf);

extern IPTR_T
AIP_buffer_payload (Buffer_Id Buf);

/*****************
 * AIP.Callbacks *
 *****************/

typedef void *CBK_Id;

/***************
 * AIP.IPaddrs *
 ***************/

typedef M32_T IPaddr;

/***********
 * AIP.NIF *
 ***********/

typedef enum { Invalid, Down, Up } Netif_State;

typedef EID Netif_Id;
#define IF_NOID (-1)

#define MAX_LL_ADDRESS_LENGTH 6

typedef struct netif {
  Netif_State State;
  char        Name[2];

  char        LL_Address[MAX_LL_ADDRESS_LENGTH];
  U8_T        LL_Address_Length;

  U16_T       MTU;

  IPaddr      IP;
  IPaddr      Mask;
  IPaddr      Broadcast;

  CBK_Id      Input_CB;
  CBK_Id      Output_CB;
  CBK_Id      Link_Output_CB;

  IPTR_T Dev;
} Netif;

typedef void (*Input_CB_T)       (Buffer_Id Buf, Netif_Id Nid);
typedef void (*Output_CB_T)      (Buffer_Id Buf, Netif_Id Nid, IPaddr Dst_Address);
typedef void (*Link_Output_CB_T) (Buffer_Id Buf, Netif_Id Nid);

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

/**************
 * AIP.EtherH *
 **************/

#define Ether_Type_ARP 0x0806
#define Ether_Type_IP  0x0800

typedef struct {} Ether_Header;
U16_T
aip__etherh__frame_type (Ether_Header M);

#define AIP_etherh_frame_type aip__etherh__frame_type

/***********************
 * Compatibility shims *
 ***********************/

#define err_t Err_T

#endif /* __AIP_H__ */
