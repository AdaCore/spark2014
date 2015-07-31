/* This file has been automatically generated from src/proto/arph.xml       */
/* DO NOT EDIT!!!                                                           */

/************
 ** ARP_Hw **
 ************/

#define ARP_Hw_Ethernet 1

/************
 ** ARP_Op **
 ************/

#define ARP_Op_Request 1
#define ARP_Op_Reply   2

/****************
 ** ARP_Header **
 ****************/

#define ARP_Header_Size 224

extern U16_T
AIP_ARPH_Hardware_Type (void *p);
extern void
AIP_Set_ARPH_Hardware_Type (void *p, U16_T v);

extern U16_T
AIP_ARPH_Protocol (void *p);
extern void
AIP_Set_ARPH_Protocol (void *p, U16_T v);

extern U8_T
AIP_ARPH_Hw_Len (void *p);
extern void
AIP_Set_ARPH_Hw_Len (void *p, U8_T v);

extern U8_T
AIP_ARPH_Pr_Len (void *p);
extern void
AIP_Set_ARPH_Pr_Len (void *p, U8_T v);

extern U16_T
AIP_ARPH_Operation (void *p);
extern void
AIP_Set_ARPH_Operation (void *p, U16_T v);

extern M32_T
AIP_ARPH_Src_IP_Address (void *p);
extern void
AIP_Set_ARPH_Src_IP_Address (void *p, M32_T v);

extern M32_T
AIP_ARPH_Dst_IP_Address (void *p);
extern void
AIP_Set_ARPH_Dst_IP_Address (void *p, M32_T v);
