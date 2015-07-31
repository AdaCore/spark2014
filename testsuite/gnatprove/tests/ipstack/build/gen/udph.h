/* This file has been automatically generated from src/proto/udph.xml       */
/* DO NOT EDIT!!!                                                           */

/****************
 ** UDP_Header **
 ****************/

#define UDP_Header_Size 64

extern U16_T
AIP_UDPH_Src_Port (void *p);
extern void
AIP_Set_UDPH_Src_Port (void *p, U16_T v);

extern U16_T
AIP_UDPH_Dst_Port (void *p);
extern void
AIP_Set_UDPH_Dst_Port (void *p, U16_T v);

extern U16_T
AIP_UDPH_Length (void *p);
extern void
AIP_Set_UDPH_Length (void *p, U16_T v);

extern M16_T
AIP_UDPH_Checksum (void *p);
extern void
AIP_Set_UDPH_Checksum (void *p, M16_T v);

/***********************
 ** UDP_Pseudo_Header **
 ***********************/

#define UDP_Pseudo_Header_Size 96

extern M32_T
AIP_UDPP_Src_Address (void *p);
extern void
AIP_Set_UDPP_Src_Address (void *p, M32_T v);

extern M32_T
AIP_UDPP_Dst_Address (void *p);
extern void
AIP_Set_UDPP_Dst_Address (void *p, M32_T v);

extern U8_T
AIP_UDPP_Zero (void *p);
extern void
AIP_Set_UDPP_Zero (void *p, U8_T v);

extern U8_T
AIP_UDPP_Protocol (void *p);
extern void
AIP_Set_UDPP_Protocol (void *p, U8_T v);

extern U16_T
AIP_UDPP_Length (void *p);
extern void
AIP_Set_UDPP_Length (void *p, U16_T v);
