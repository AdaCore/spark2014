--  This file has been automatically generated from src/proto/tcph.xml
--  DO NOT EDIT!!!

pragma Warnings (Off);
pragma Style_Checks ("NM32766");
pragma Ada_2012;

package body AIP.TCPH with
  SPARK_Mode => Off
is

   function  TCPH_Src_Port        (P : System.Address) return AIP.U16_T is
      M : TCP_Header with Address => P, Import;
   begin
      return M.Src_Port;
   end TCPH_Src_Port;

   procedure Set_TCPH_Src_Port    (P : System.Address; V : AIP.U16_T) is
      M : TCP_Header with Address => P, Import;
   begin
      M.Src_Port := V;
   end Set_TCPH_Src_Port;

   function  TCPH_Dst_Port        (P : System.Address) return AIP.U16_T is
      M : TCP_Header with Address => P, Import;
   begin
      return M.Dst_Port;
   end TCPH_Dst_Port;

   procedure Set_TCPH_Dst_Port    (P : System.Address; V : AIP.U16_T) is
      M : TCP_Header with Address => P, Import;
   begin
      M.Dst_Port := V;
   end Set_TCPH_Dst_Port;

   function  TCPH_Seq_Num         (P : System.Address) return AIP.M32_T is
      M : TCP_Header with Address => P, Import;
   begin
      return M.Seq_Num;
   end TCPH_Seq_Num;

   procedure Set_TCPH_Seq_Num     (P : System.Address; V : AIP.M32_T) is
      M : TCP_Header with Address => P, Import;
   begin
      M.Seq_Num := V;
   end Set_TCPH_Seq_Num;

   function  TCPH_Ack_Num         (P : System.Address) return AIP.M32_T is
      M : TCP_Header with Address => P, Import;
   begin
      return M.Ack_Num;
   end TCPH_Ack_Num;

   procedure Set_TCPH_Ack_Num     (P : System.Address; V : AIP.M32_T) is
      M : TCP_Header with Address => P, Import;
   begin
      M.Ack_Num := V;
   end Set_TCPH_Ack_Num;

   function  TCPH_Data_Offset     (P : System.Address) return AIP.U4_T is
      M : TCP_Header with Address => P, Import;
   begin
      return M.Data_Offset;
   end TCPH_Data_Offset;

   procedure Set_TCPH_Data_Offset (P : System.Address; V : AIP.U4_T) is
      M : TCP_Header with Address => P, Import;
   begin
      M.Data_Offset := V;
   end Set_TCPH_Data_Offset;

   function  TCPH_Reserved        (P : System.Address) return AIP.U6_T is
      M : TCP_Header with Address => P, Import;
   begin
      return M.Reserved;
   end TCPH_Reserved;

   procedure Set_TCPH_Reserved    (P : System.Address; V : AIP.U6_T) is
      M : TCP_Header with Address => P, Import;
   begin
      M.Reserved := V;
   end Set_TCPH_Reserved;

   function  TCPH_Urg             (P : System.Address) return AIP.U1_T is
      M : TCP_Header with Address => P, Import;
   begin
      return M.Urg;
   end TCPH_Urg;

   procedure Set_TCPH_Urg         (P : System.Address; V : AIP.U1_T) is
      M : TCP_Header with Address => P, Import;
   begin
      M.Urg := V;
   end Set_TCPH_Urg;

   function  TCPH_Ack             (P : System.Address) return AIP.U1_T is
      M : TCP_Header with Address => P, Import;
   begin
      return M.Ack;
   end TCPH_Ack;

   procedure Set_TCPH_Ack         (P : System.Address; V : AIP.U1_T) is
      M : TCP_Header with Address => P, Import;
   begin
      M.Ack := V;
   end Set_TCPH_Ack;

   function  TCPH_Psh             (P : System.Address) return AIP.U1_T is
      M : TCP_Header with Address => P, Import;
   begin
      return M.Psh;
   end TCPH_Psh;

   procedure Set_TCPH_Psh         (P : System.Address; V : AIP.U1_T) is
      M : TCP_Header with Address => P, Import;
   begin
      M.Psh := V;
   end Set_TCPH_Psh;

   function  TCPH_Rst             (P : System.Address) return AIP.U1_T is
      M : TCP_Header with Address => P, Import;
   begin
      return M.Rst;
   end TCPH_Rst;

   procedure Set_TCPH_Rst         (P : System.Address; V : AIP.U1_T) is
      M : TCP_Header with Address => P, Import;
   begin
      M.Rst := V;
   end Set_TCPH_Rst;

   function  TCPH_Syn             (P : System.Address) return AIP.U1_T is
      M : TCP_Header with Address => P, Import;
   begin
      return M.Syn;
   end TCPH_Syn;

   procedure Set_TCPH_Syn         (P : System.Address; V : AIP.U1_T) is
      M : TCP_Header with Address => P, Import;
   begin
      M.Syn := V;
   end Set_TCPH_Syn;

   function  TCPH_Fin             (P : System.Address) return AIP.U1_T is
      M : TCP_Header with Address => P, Import;
   begin
      return M.Fin;
   end TCPH_Fin;

   procedure Set_TCPH_Fin         (P : System.Address; V : AIP.U1_T) is
      M : TCP_Header with Address => P, Import;
   begin
      M.Fin := V;
   end Set_TCPH_Fin;

   function  TCPH_Window          (P : System.Address) return AIP.U16_T is
      M : TCP_Header with Address => P, Import;
   begin
      return M.Window;
   end TCPH_Window;

   procedure Set_TCPH_Window      (P : System.Address; V : AIP.U16_T) is
      M : TCP_Header with Address => P, Import;
   begin
      M.Window := V;
   end Set_TCPH_Window;

   function  TCPH_Checksum        (P : System.Address) return AIP.M16_T is
      M : TCP_Header with Address => P, Import;
   begin
      return M.Checksum;
   end TCPH_Checksum;

   procedure Set_TCPH_Checksum    (P : System.Address; V : AIP.M16_T) is
      M : TCP_Header with Address => P, Import;
   begin
      M.Checksum := V;
   end Set_TCPH_Checksum;

   function  TCPH_Urgent_Ptr      (P : System.Address) return AIP.U16_T is
      M : TCP_Header with Address => P, Import;
   begin
      return M.Urgent_Ptr;
   end TCPH_Urgent_Ptr;

   procedure Set_TCPH_Urgent_Ptr  (P : System.Address; V : AIP.U16_T) is
      M : TCP_Header with Address => P, Import;
   begin
      M.Urgent_Ptr := V;
   end Set_TCPH_Urgent_Ptr;

   function  TCPP_Src_Address     (P : System.Address) return AIP.M32_T is
      M : TCP_Pseudo_Header with Address => P, Import;
   begin
      return M.Src_Address;
   end TCPP_Src_Address;

   procedure Set_TCPP_Src_Address (P : System.Address; V : AIP.M32_T) is
      M : TCP_Pseudo_Header with Address => P, Import;
   begin
      M.Src_Address := V;
   end Set_TCPP_Src_Address;

   function  TCPP_Dst_Address     (P : System.Address) return AIP.M32_T is
      M : TCP_Pseudo_Header with Address => P, Import;
   begin
      return M.Dst_Address;
   end TCPP_Dst_Address;

   procedure Set_TCPP_Dst_Address (P : System.Address; V : AIP.M32_T) is
      M : TCP_Pseudo_Header with Address => P, Import;
   begin
      M.Dst_Address := V;
   end Set_TCPP_Dst_Address;

   function  TCPP_Zero            (P : System.Address) return AIP.U8_T is
      M : TCP_Pseudo_Header with Address => P, Import;
   begin
      return M.Zero;
   end TCPP_Zero;

   procedure Set_TCPP_Zero        (P : System.Address; V : AIP.U8_T) is
      M : TCP_Pseudo_Header with Address => P, Import;
   begin
      M.Zero := V;
   end Set_TCPP_Zero;

   function  TCPP_Protocol        (P : System.Address) return AIP.U8_T is
      M : TCP_Pseudo_Header with Address => P, Import;
   begin
      return M.Protocol;
   end TCPP_Protocol;

   procedure Set_TCPP_Protocol    (P : System.Address; V : AIP.U8_T) is
      M : TCP_Pseudo_Header with Address => P, Import;
   begin
      M.Protocol := V;
   end Set_TCPP_Protocol;

   function  TCPP_Length          (P : System.Address) return AIP.U16_T is
      M : TCP_Pseudo_Header with Address => P, Import;
   begin
      return M.Length;
   end TCPP_Length;

   procedure Set_TCPP_Length      (P : System.Address; V : AIP.U16_T) is
      M : TCP_Pseudo_Header with Address => P, Import;
   begin
      M.Length := V;
   end Set_TCPP_Length;
end AIP.TCPH;
