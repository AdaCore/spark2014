/* This file has been automatically generated from src/proto/tcph.xml       */
/* DO NOT EDIT!!!                                                           */

/****************
 ** TCP_Header **
 ****************/

#define TCP_Header_Size 160

extern U16_T
AIP_TCPH_Src_Port (void *p);
extern void
AIP_Set_TCPH_Src_Port (void *p, U16_T v);

extern U16_T
AIP_TCPH_Dst_Port (void *p);
extern void
AIP_Set_TCPH_Dst_Port (void *p, U16_T v);

extern M32_T
AIP_TCPH_Seq_Num (void *p);
extern void
AIP_Set_TCPH_Seq_Num (void *p, M32_T v);

extern M32_T
AIP_TCPH_Ack_Num (void *p);
extern void
AIP_Set_TCPH_Ack_Num (void *p, M32_T v);

extern U4_T
AIP_TCPH_Data_Offset (void *p);
extern void
AIP_Set_TCPH_Data_Offset (void *p, U4_T v);

extern U6_T
AIP_TCPH_Reserved (void *p);
extern void
AIP_Set_TCPH_Reserved (void *p, U6_T v);

extern U1_T
AIP_TCPH_Urg (void *p);
extern void
AIP_Set_TCPH_Urg (void *p, U1_T v);

extern U1_T
AIP_TCPH_Ack (void *p);
extern void
AIP_Set_TCPH_Ack (void *p, U1_T v);

extern U1_T
AIP_TCPH_Psh (void *p);
extern void
AIP_Set_TCPH_Psh (void *p, U1_T v);

extern U1_T
AIP_TCPH_Rst (void *p);
extern void
AIP_Set_TCPH_Rst (void *p, U1_T v);

extern U1_T
AIP_TCPH_Syn (void *p);
extern void
AIP_Set_TCPH_Syn (void *p, U1_T v);

extern U1_T
AIP_TCPH_Fin (void *p);
extern void
AIP_Set_TCPH_Fin (void *p, U1_T v);

extern U16_T
AIP_TCPH_Window (void *p);
extern void
AIP_Set_TCPH_Window (void *p, U16_T v);

extern M16_T
AIP_TCPH_Checksum (void *p);
extern void
AIP_Set_TCPH_Checksum (void *p, M16_T v);

extern U16_T
AIP_TCPH_Urgent_Ptr (void *p);
extern void
AIP_Set_TCPH_Urgent_Ptr (void *p, U16_T v);

/****************
 ** TCP_Option **
 ****************/

#define TCP_Option_End       0
#define TCP_Option_NOP       1
#define TCP_Option_MSS       2
#define TCP_Option_Win_Scale 3

/***********************
 ** TCP_Pseudo_Header **
 ***********************/

#define TCP_Pseudo_Header_Size 96

extern M32_T
AIP_TCPP_Src_Address (void *p);
extern void
AIP_Set_TCPP_Src_Address (void *p, M32_T v);

extern M32_T
AIP_TCPP_Dst_Address (void *p);
extern void
AIP_Set_TCPP_Dst_Address (void *p, M32_T v);

extern U8_T
AIP_TCPP_Zero (void *p);
extern void
AIP_Set_TCPP_Zero (void *p, U8_T v);

extern U8_T
AIP_TCPP_Protocol (void *p);
extern void
AIP_Set_TCPP_Protocol (void *p, U8_T v);

extern U16_T
AIP_TCPP_Length (void *p);
extern void
AIP_Set_TCPP_Length (void *p, U16_T v);
