--  This file has been automatically generated from src/proto/tcph.xml
--  DO NOT EDIT!!!

pragma Warnings (Off);
pragma Style_Checks ("NM32766");
pragma Ada_2012;

with System;

package AIP.TCPH is

   pragma Pure;

   ----------------
   -- TCP_Header --
   ----------------

   type TCP_Header is private;
   TCP_Header_Size : constant := 160;

   function  TCPH_Src_Port        (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_TCPH_Src_Port    (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPH_Src_Port, "AIP_TCPH_Src_Port");
   pragma Export (C, Set_TCPH_Src_Port, "AIP_Set_TCPH_Src_Port");

   function  TCPH_Dst_Port        (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_TCPH_Dst_Port    (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPH_Dst_Port, "AIP_TCPH_Dst_Port");
   pragma Export (C, Set_TCPH_Dst_Port, "AIP_Set_TCPH_Dst_Port");

   function  TCPH_Seq_Num         (P : System.Address) return AIP.M32_T
     with Inline;
   procedure Set_TCPH_Seq_Num     (P : System.Address; V : AIP.M32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPH_Seq_Num, "AIP_TCPH_Seq_Num");
   pragma Export (C, Set_TCPH_Seq_Num, "AIP_Set_TCPH_Seq_Num");

   function  TCPH_Ack_Num         (P : System.Address) return AIP.M32_T
     with Inline;
   procedure Set_TCPH_Ack_Num     (P : System.Address; V : AIP.M32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPH_Ack_Num, "AIP_TCPH_Ack_Num");
   pragma Export (C, Set_TCPH_Ack_Num, "AIP_Set_TCPH_Ack_Num");

   function  TCPH_Data_Offset     (P : System.Address) return AIP.U4_T
     with Inline;
   procedure Set_TCPH_Data_Offset (P : System.Address; V : AIP.U4_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPH_Data_Offset, "AIP_TCPH_Data_Offset");
   pragma Export (C, Set_TCPH_Data_Offset, "AIP_Set_TCPH_Data_Offset");

   function  TCPH_Reserved        (P : System.Address) return AIP.U6_T
     with Inline;
   procedure Set_TCPH_Reserved    (P : System.Address; V : AIP.U6_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPH_Reserved, "AIP_TCPH_Reserved");
   pragma Export (C, Set_TCPH_Reserved, "AIP_Set_TCPH_Reserved");

   function  TCPH_Urg             (P : System.Address) return AIP.U1_T
     with Inline;
   procedure Set_TCPH_Urg         (P : System.Address; V : AIP.U1_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPH_Urg, "AIP_TCPH_Urg");
   pragma Export (C, Set_TCPH_Urg, "AIP_Set_TCPH_Urg");

   function  TCPH_Ack             (P : System.Address) return AIP.U1_T
     with Inline;
   procedure Set_TCPH_Ack         (P : System.Address; V : AIP.U1_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPH_Ack, "AIP_TCPH_Ack");
   pragma Export (C, Set_TCPH_Ack, "AIP_Set_TCPH_Ack");

   function  TCPH_Psh             (P : System.Address) return AIP.U1_T
     with Inline;
   procedure Set_TCPH_Psh         (P : System.Address; V : AIP.U1_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPH_Psh, "AIP_TCPH_Psh");
   pragma Export (C, Set_TCPH_Psh, "AIP_Set_TCPH_Psh");

   function  TCPH_Rst             (P : System.Address) return AIP.U1_T
     with Inline;
   procedure Set_TCPH_Rst         (P : System.Address; V : AIP.U1_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPH_Rst, "AIP_TCPH_Rst");
   pragma Export (C, Set_TCPH_Rst, "AIP_Set_TCPH_Rst");

   function  TCPH_Syn             (P : System.Address) return AIP.U1_T
     with Inline;
   procedure Set_TCPH_Syn         (P : System.Address; V : AIP.U1_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPH_Syn, "AIP_TCPH_Syn");
   pragma Export (C, Set_TCPH_Syn, "AIP_Set_TCPH_Syn");

   function  TCPH_Fin             (P : System.Address) return AIP.U1_T
     with Inline;
   procedure Set_TCPH_Fin         (P : System.Address; V : AIP.U1_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPH_Fin, "AIP_TCPH_Fin");
   pragma Export (C, Set_TCPH_Fin, "AIP_Set_TCPH_Fin");

   function  TCPH_Window          (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_TCPH_Window      (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPH_Window, "AIP_TCPH_Window");
   pragma Export (C, Set_TCPH_Window, "AIP_Set_TCPH_Window");

   function  TCPH_Checksum        (P : System.Address) return AIP.M16_T
     with Inline;
   procedure Set_TCPH_Checksum    (P : System.Address; V : AIP.M16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPH_Checksum, "AIP_TCPH_Checksum");
   pragma Export (C, Set_TCPH_Checksum, "AIP_Set_TCPH_Checksum");

   function  TCPH_Urgent_Ptr      (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_TCPH_Urgent_Ptr  (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPH_Urgent_Ptr, "AIP_TCPH_Urgent_Ptr");
   pragma Export (C, Set_TCPH_Urgent_Ptr, "AIP_Set_TCPH_Urgent_Ptr");

   ----------------
   -- TCP_Option --
   ----------------

   TCP_Option_End       : constant := 0;
   TCP_Option_NOP       : constant := 1;
   TCP_Option_MSS       : constant := 2;
   TCP_Option_Win_Scale : constant := 3;

   -----------------------
   -- TCP_Pseudo_Header --
   -----------------------

   type TCP_Pseudo_Header is private;
   TCP_Pseudo_Header_Size : constant := 96;

   function  TCPP_Src_Address     (P : System.Address) return AIP.M32_T
     with Inline;
   procedure Set_TCPP_Src_Address (P : System.Address; V : AIP.M32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPP_Src_Address, "AIP_TCPP_Src_Address");
   pragma Export (C, Set_TCPP_Src_Address, "AIP_Set_TCPP_Src_Address");

   function  TCPP_Dst_Address     (P : System.Address) return AIP.M32_T
     with Inline;
   procedure Set_TCPP_Dst_Address (P : System.Address; V : AIP.M32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPP_Dst_Address, "AIP_TCPP_Dst_Address");
   pragma Export (C, Set_TCPP_Dst_Address, "AIP_Set_TCPP_Dst_Address");

   function  TCPP_Zero            (P : System.Address) return AIP.U8_T
     with Inline;
   procedure Set_TCPP_Zero        (P : System.Address; V : AIP.U8_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPP_Zero, "AIP_TCPP_Zero");
   pragma Export (C, Set_TCPP_Zero, "AIP_Set_TCPP_Zero");

   function  TCPP_Protocol        (P : System.Address) return AIP.U8_T
     with Inline;
   procedure Set_TCPP_Protocol    (P : System.Address; V : AIP.U8_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPP_Protocol, "AIP_TCPP_Protocol");
   pragma Export (C, Set_TCPP_Protocol, "AIP_Set_TCPP_Protocol");

   function  TCPP_Length          (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_TCPP_Length      (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, TCPP_Length, "AIP_TCPP_Length");
   pragma Export (C, Set_TCPP_Length, "AIP_Set_TCPP_Length");

private

   type TCP_Header is record
      Src_Port    : AIP.U16_T;
      Dst_Port    : AIP.U16_T;
      Seq_Num     : AIP.M32_T;
      Ack_Num     : AIP.M32_T;
      Data_Offset : AIP.U4_T;
      Reserved    : AIP.U6_T;
      Urg         : AIP.U1_T;
      Ack         : AIP.U1_T;
      Psh         : AIP.U1_T;
      Rst         : AIP.U1_T;
      Syn         : AIP.U1_T;
      Fin         : AIP.U1_T;
      Window      : AIP.U16_T;
      Checksum    : AIP.M16_T;
      Urgent_Ptr  : AIP.U16_T;
   end record
   with
     Alignment            => 1,
     Bit_Order            => System.High_Order_First,
     Scalar_Storage_Order => System.High_Order_First;

   for TCP_Header use record
      Src_Port    at 0 range 0 .. 15;
      Dst_Port    at 0 range 16 .. 31;
      Seq_Num     at 4 range 0 .. 31;
      Ack_Num     at 8 range 0 .. 31;
      Data_Offset at 12 range 0 .. 3;
      Reserved    at 12 range 4 .. 9;
      Urg         at 12 range 10 .. 10;
      Ack         at 12 range 11 .. 11;
      Psh         at 12 range 12 .. 12;
      Rst         at 12 range 13 .. 13;
      Syn         at 12 range 14 .. 14;
      Fin         at 12 range 15 .. 15;
      Window      at 12 range 16 .. 31;
      Checksum    at 16 range 0 .. 15;
      Urgent_Ptr  at 16 range 16 .. 31;
   end record;

   type TCP_Pseudo_Header is record
      Src_Address : AIP.M32_T;
      Dst_Address : AIP.M32_T;
      Zero        : AIP.U8_T;
      Protocol    : AIP.U8_T;
      Length      : AIP.U16_T;
   end record
   with
     Alignment            => 1,
     Bit_Order            => System.High_Order_First,
     Scalar_Storage_Order => System.High_Order_First;

   for TCP_Pseudo_Header use record
      Src_Address at 0 range 0 .. 31;
      Dst_Address at 4 range 0 .. 31;
      Zero        at 8 range 0 .. 7;
      Protocol    at 8 range 8 .. 15;
      Length      at 8 range 16 .. 31;
   end record;
end AIP.TCPH;
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
