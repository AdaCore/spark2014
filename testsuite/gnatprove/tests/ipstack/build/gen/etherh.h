/* This file has been automatically generated from src/proto/etherh.xml     */
/* DO NOT EDIT!!!                                                           */

/****************
 ** Ether_Type **
 ****************/

#define Ether_Type_ARP        0x806
#define Ether_Type_IP         0x800
#define Ether_Type_PPPoE_Disc 0x8863
#define Ether_Type_PPPoE      0x8864

/******************
 ** Ether_Header **
 ******************/

#define Ether_Header_Size 112

extern U16_T
AIP_EtherH_Frame_Type (void *p);
extern void
AIP_Set_EtherH_Frame_Type (void *p, U16_T v);
