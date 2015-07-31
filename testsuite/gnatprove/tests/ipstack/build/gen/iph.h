/* This file has been automatically generated from src/proto/iph.xml        */
/* DO NOT EDIT!!!                                                           */

/**************
 ** IP_Proto **
 **************/

#define IP_Proto_UDP  17
#define IP_Proto_TCP  6
#define IP_Proto_ICMP 1

/***************
 ** IP_Header **
 ***************/

#define IP_Header_Size 160

extern U4_T
AIP_IPH_Version (void *p);
extern void
AIP_Set_IPH_Version (void *p, U4_T v);

extern U4_T
AIP_IPH_IHL (void *p);
extern void
AIP_Set_IPH_IHL (void *p, U4_T v);

extern U8_T
AIP_IPH_TOS (void *p);
extern void
AIP_Set_IPH_TOS (void *p, U8_T v);

extern U16_T
AIP_IPH_Length (void *p);
extern void
AIP_Set_IPH_Length (void *p, U16_T v);

extern M16_T
AIP_IPH_Ident (void *p);
extern void
AIP_Set_IPH_Ident (void *p, M16_T v);

extern U3_T
AIP_IPH_Flags (void *p);
extern void
AIP_Set_IPH_Flags (void *p, U3_T v);

extern U13_T
AIP_IPH_Frag_Offset (void *p);
extern void
AIP_Set_IPH_Frag_Offset (void *p, U13_T v);

extern U8_T
AIP_IPH_TTL (void *p);
extern void
AIP_Set_IPH_TTL (void *p, U8_T v);

extern U8_T
AIP_IPH_Protocol (void *p);
extern void
AIP_Set_IPH_Protocol (void *p, U8_T v);

extern M16_T
AIP_IPH_Checksum (void *p);
extern void
AIP_Set_IPH_Checksum (void *p, M16_T v);

extern M32_T
AIP_IPH_Src_Address (void *p);
extern void
AIP_Set_IPH_Src_Address (void *p, M32_T v);

extern M32_T
AIP_IPH_Dst_Address (void *p);
extern void
AIP_Set_IPH_Dst_Address (void *p, M32_T v);
