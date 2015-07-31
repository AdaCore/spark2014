/* This file has been automatically generated from src/proto/icmph.xml      */
/* DO NOT EDIT!!!                                                           */

/***************
 ** ICMP_Type **
 ***************/

#define ICMP_Type_Echo_Reply        0
#define ICMP_Type_Dest_Unreachable  3
#define ICMP_Type_Source_Quench     4
#define ICMP_Type_Redirect          5
#define ICMP_Type_Echo              8
#define ICMP_Type_Time_Exceeded     11
#define ICMP_Type_Parameter_Problem 12
#define ICMP_Type_Timestamp         13
#define ICMP_Type_Timestamp_Reply   14
#define ICMP_Type_Info_Request      15
#define ICMP_Type_Info_Reply        16

/***********************
 ** ICMP_Unreach_Code **
 ***********************/

#define ICMP_Unreach_Code_Net_Unreachable   0
#define ICMP_Unreach_Code_Host_Unreachable  1
#define ICMP_Unreach_Code_Proto_Unreachable 2
#define ICMP_Unreach_Code_Port_Unreachable  3
#define ICMP_Unreach_Code_Must_Fragment     4
#define ICMP_Unreach_Code_Src_Route_Failed  5

/************************
 ** ICMP_Redirect_Code **
 ************************/

#define ICMP_Redirect_Code_Redirect_Net      0
#define ICMP_Redirect_Code_Redirect_Host     1
#define ICMP_Redirect_Code_Redirect_TOS_Net  2
#define ICMP_Redirect_Code_Redirect_TOS_Host 3

/*****************
 ** ICMP_Header **
 *****************/

#define ICMP_Header_Size 32

extern U8_T
AIP_ICMPH_I_Type (void *p);
extern void
AIP_Set_ICMPH_I_Type (void *p, U8_T v);

extern U8_T
AIP_ICMPH_Code (void *p);
extern void
AIP_Set_ICMPH_Code (void *p, U8_T v);

extern M16_T
AIP_ICMPH_Checksum (void *p);
extern void
AIP_Set_ICMPH_Checksum (void *p, M16_T v);

/***************************
 ** ICMP_Timestamp_Header **
 ***************************/

#define ICMP_Timestamp_Header_Size 160

extern U32_T
AIP_ICMP_TSH_ICMPH (void *p);
extern void
AIP_Set_ICMP_TSH_ICMPH (void *p, U32_T v);

extern U16_T
AIP_ICMP_TSH_Identifier (void *p);
extern void
AIP_Set_ICMP_TSH_Identifier (void *p, U16_T v);

extern U16_T
AIP_ICMP_TSH_Sequence (void *p);
extern void
AIP_Set_ICMP_TSH_Sequence (void *p, U16_T v);

extern U32_T
AIP_ICMP_TSH_Originate (void *p);
extern void
AIP_Set_ICMP_TSH_Originate (void *p, U32_T v);

extern U32_T
AIP_ICMP_TSH_Receive (void *p);
extern void
AIP_Set_ICMP_TSH_Receive (void *p, U32_T v);

extern U32_T
AIP_ICMP_TSH_Transmit (void *p);
extern void
AIP_Set_ICMP_TSH_Transmit (void *p, U32_T v);

/**************************
 ** ICMP_Redirect_Header **
 **************************/

#define ICMP_Redirect_Header_Size 64

extern U32_T
AIP_ICMP_RH_ICMPH (void *p);
extern void
AIP_Set_ICMP_RH_ICMPH (void *p, U32_T v);

extern U32_T
AIP_ICMP_RH_Gateway_Address (void *p);
extern void
AIP_Set_ICMP_RH_Gateway_Address (void *p, U32_T v);

/*************************
 ** ICMP_Generic_Header **
 *************************/

#define ICMP_Generic_Header_Size 64

extern U32_T
AIP_ICMP_Generic_H_ICMPH (void *p);
extern void
AIP_Set_ICMP_Generic_H_ICMPH (void *p, U32_T v);

extern U8_T
AIP_ICMP_Generic_H_Pointer (void *p);
extern void
AIP_Set_ICMP_Generic_H_Pointer (void *p, U8_T v);

extern U24_T
AIP_ICMP_Generic_H_Unused (void *p);
extern void
AIP_Set_ICMP_Generic_H_Unused (void *p, U24_T v);
