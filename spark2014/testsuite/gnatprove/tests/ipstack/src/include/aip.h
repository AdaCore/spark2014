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

typedef unsigned long   M32_T;

typedef void           *IPTR_T;

typedef unsigned char   Err_T;

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

typedef struct netif {
  IPaddr IP;
  IPaddr Mask;
  IPaddr Broadcast;

  CBK_Id Input_CB;
  CBK_Id Output_CB;

  IPTR_T Dev;
} Netif;

/***********************
 * Compatibility shims *
 ***********************/

#define err_t Err_T

#define state Dev
/* Driver-private component of struct netif */

#endif /* __AIP_H__ */
