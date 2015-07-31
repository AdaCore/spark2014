--  This file has been automatically generated from src/proto/iph.xml
--  DO NOT EDIT!!!

pragma Warnings (Off);
pragma Style_Checks ("NM32766");
pragma Ada_2012;

with System;

package AIP.IPH is

   pragma Pure;

   --------------
   -- IP_Proto --
   --------------

   IP_Proto_UDP  : constant := 17;
   IP_Proto_TCP  : constant := 6;
   IP_Proto_ICMP : constant := 1;

   ---------------
   -- IP_Header --
   ---------------

   type IP_Header is private;
   IP_Header_Size : constant := 160;

   function  IPH_Version         (P : System.Address) return AIP.U4_T
     with Inline;
   procedure Set_IPH_Version     (P : System.Address; V : AIP.U4_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, IPH_Version, "AIP_IPH_Version");
   pragma Export (C, Set_IPH_Version, "AIP_Set_IPH_Version");

   function  IPH_IHL             (P : System.Address) return AIP.U4_T
     with Inline;
   procedure Set_IPH_IHL         (P : System.Address; V : AIP.U4_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, IPH_IHL, "AIP_IPH_IHL");
   pragma Export (C, Set_IPH_IHL, "AIP_Set_IPH_IHL");

   function  IPH_TOS             (P : System.Address) return AIP.U8_T
     with Inline;
   procedure Set_IPH_TOS         (P : System.Address; V : AIP.U8_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, IPH_TOS, "AIP_IPH_TOS");
   pragma Export (C, Set_IPH_TOS, "AIP_Set_IPH_TOS");

   function  IPH_Length          (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_IPH_Length      (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, IPH_Length, "AIP_IPH_Length");
   pragma Export (C, Set_IPH_Length, "AIP_Set_IPH_Length");

   function  IPH_Ident           (P : System.Address) return AIP.M16_T
     with Inline;
   procedure Set_IPH_Ident       (P : System.Address; V : AIP.M16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, IPH_Ident, "AIP_IPH_Ident");
   pragma Export (C, Set_IPH_Ident, "AIP_Set_IPH_Ident");

   function  IPH_Flags           (P : System.Address) return AIP.U3_T
     with Inline;
   procedure Set_IPH_Flags       (P : System.Address; V : AIP.U3_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, IPH_Flags, "AIP_IPH_Flags");
   pragma Export (C, Set_IPH_Flags, "AIP_Set_IPH_Flags");

   function  IPH_Frag_Offset     (P : System.Address) return AIP.U13_T
     with Inline;
   procedure Set_IPH_Frag_Offset (P : System.Address; V : AIP.U13_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, IPH_Frag_Offset, "AIP_IPH_Frag_Offset");
   pragma Export (C, Set_IPH_Frag_Offset, "AIP_Set_IPH_Frag_Offset");

   function  IPH_TTL             (P : System.Address) return AIP.U8_T
     with Inline;
   procedure Set_IPH_TTL         (P : System.Address; V : AIP.U8_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, IPH_TTL, "AIP_IPH_TTL");
   pragma Export (C, Set_IPH_TTL, "AIP_Set_IPH_TTL");

   function  IPH_Protocol        (P : System.Address) return AIP.U8_T
     with Inline;
   procedure Set_IPH_Protocol    (P : System.Address; V : AIP.U8_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, IPH_Protocol, "AIP_IPH_Protocol");
   pragma Export (C, Set_IPH_Protocol, "AIP_Set_IPH_Protocol");

   function  IPH_Checksum        (P : System.Address) return AIP.M16_T
     with Inline;
   procedure Set_IPH_Checksum    (P : System.Address; V : AIP.M16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, IPH_Checksum, "AIP_IPH_Checksum");
   pragma Export (C, Set_IPH_Checksum, "AIP_Set_IPH_Checksum");

   function  IPH_Src_Address     (P : System.Address) return AIP.M32_T
     with Inline;
   procedure Set_IPH_Src_Address (P : System.Address; V : AIP.M32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, IPH_Src_Address, "AIP_IPH_Src_Address");
   pragma Export (C, Set_IPH_Src_Address, "AIP_Set_IPH_Src_Address");

   function  IPH_Dst_Address     (P : System.Address) return AIP.M32_T
     with Inline;
   procedure Set_IPH_Dst_Address (P : System.Address; V : AIP.M32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, IPH_Dst_Address, "AIP_IPH_Dst_Address");
   pragma Export (C, Set_IPH_Dst_Address, "AIP_Set_IPH_Dst_Address");

private

   type IP_Header is record
      Version     : AIP.U4_T;
      IHL         : AIP.U4_T;
      TOS         : AIP.U8_T;
      Length      : AIP.U16_T;
      Ident       : AIP.M16_T;
      Flags       : AIP.U3_T;
      Frag_Offset : AIP.U13_T;
      TTL         : AIP.U8_T;
      Protocol    : AIP.U8_T;
      Checksum    : AIP.M16_T;
      Src_Address : AIP.M32_T;
      Dst_Address : AIP.M32_T;
   end record
   with
     Alignment            => 1,
     Bit_Order            => System.High_Order_First,
     Scalar_Storage_Order => System.High_Order_First;

   for IP_Header use record
      Version     at 0 range 0 .. 3;
      IHL         at 0 range 4 .. 7;
      TOS         at 0 range 8 .. 15;
      Length      at 0 range 16 .. 31;
      Ident       at 4 range 0 .. 15;
      Flags       at 4 range 16 .. 18;
      Frag_Offset at 4 range 19 .. 31;
      TTL         at 8 range 0 .. 7;
      Protocol    at 8 range 8 .. 15;
      Checksum    at 8 range 16 .. 31;
      Src_Address at 12 range 0 .. 31;
      Dst_Address at 16 range 0 .. 31;
   end record;
end AIP.IPH;
--  This file has been automatically generated from src/proto/iph.xml
--  DO NOT EDIT!!!

pragma Warnings (Off);
pragma Style_Checks ("NM32766");
pragma Ada_2012;

package body AIP.IPH with
  SPARK_Mode => Off
is

   function  IPH_Version         (P : System.Address) return AIP.U4_T is
      M : IP_Header with Address => P, Import;
   begin
      return M.Version;
   end IPH_Version;

   procedure Set_IPH_Version     (P : System.Address; V : AIP.U4_T) is
      M : IP_Header with Address => P, Import;
   begin
      M.Version := V;
   end Set_IPH_Version;

   function  IPH_IHL             (P : System.Address) return AIP.U4_T is
      M : IP_Header with Address => P, Import;
   begin
      return M.IHL;
   end IPH_IHL;

   procedure Set_IPH_IHL         (P : System.Address; V : AIP.U4_T) is
      M : IP_Header with Address => P, Import;
   begin
      M.IHL := V;
   end Set_IPH_IHL;

   function  IPH_TOS             (P : System.Address) return AIP.U8_T is
      M : IP_Header with Address => P, Import;
   begin
      return M.TOS;
   end IPH_TOS;

   procedure Set_IPH_TOS         (P : System.Address; V : AIP.U8_T) is
      M : IP_Header with Address => P, Import;
   begin
      M.TOS := V;
   end Set_IPH_TOS;

   function  IPH_Length          (P : System.Address) return AIP.U16_T is
      M : IP_Header with Address => P, Import;
   begin
      return M.Length;
   end IPH_Length;

   procedure Set_IPH_Length      (P : System.Address; V : AIP.U16_T) is
      M : IP_Header with Address => P, Import;
   begin
      M.Length := V;
   end Set_IPH_Length;

   function  IPH_Ident           (P : System.Address) return AIP.M16_T is
      M : IP_Header with Address => P, Import;
   begin
      return M.Ident;
   end IPH_Ident;

   procedure Set_IPH_Ident       (P : System.Address; V : AIP.M16_T) is
      M : IP_Header with Address => P, Import;
   begin
      M.Ident := V;
   end Set_IPH_Ident;

   function  IPH_Flags           (P : System.Address) return AIP.U3_T is
      M : IP_Header with Address => P, Import;
   begin
      return M.Flags;
   end IPH_Flags;

   procedure Set_IPH_Flags       (P : System.Address; V : AIP.U3_T) is
      M : IP_Header with Address => P, Import;
   begin
      M.Flags := V;
   end Set_IPH_Flags;

   function  IPH_Frag_Offset     (P : System.Address) return AIP.U13_T is
      M : IP_Header with Address => P, Import;
   begin
      return M.Frag_Offset;
   end IPH_Frag_Offset;

   procedure Set_IPH_Frag_Offset (P : System.Address; V : AIP.U13_T) is
      M : IP_Header with Address => P, Import;
   begin
      M.Frag_Offset := V;
   end Set_IPH_Frag_Offset;

   function  IPH_TTL             (P : System.Address) return AIP.U8_T is
      M : IP_Header with Address => P, Import;
   begin
      return M.TTL;
   end IPH_TTL;

   procedure Set_IPH_TTL         (P : System.Address; V : AIP.U8_T) is
      M : IP_Header with Address => P, Import;
   begin
      M.TTL := V;
   end Set_IPH_TTL;

   function  IPH_Protocol        (P : System.Address) return AIP.U8_T is
      M : IP_Header with Address => P, Import;
   begin
      return M.Protocol;
   end IPH_Protocol;

   procedure Set_IPH_Protocol    (P : System.Address; V : AIP.U8_T) is
      M : IP_Header with Address => P, Import;
   begin
      M.Protocol := V;
   end Set_IPH_Protocol;

   function  IPH_Checksum        (P : System.Address) return AIP.M16_T is
      M : IP_Header with Address => P, Import;
   begin
      return M.Checksum;
   end IPH_Checksum;

   procedure Set_IPH_Checksum    (P : System.Address; V : AIP.M16_T) is
      M : IP_Header with Address => P, Import;
   begin
      M.Checksum := V;
   end Set_IPH_Checksum;

   function  IPH_Src_Address     (P : System.Address) return AIP.M32_T is
      M : IP_Header with Address => P, Import;
   begin
      return M.Src_Address;
   end IPH_Src_Address;

   procedure Set_IPH_Src_Address (P : System.Address; V : AIP.M32_T) is
      M : IP_Header with Address => P, Import;
   begin
      M.Src_Address := V;
   end Set_IPH_Src_Address;

   function  IPH_Dst_Address     (P : System.Address) return AIP.M32_T is
      M : IP_Header with Address => P, Import;
   begin
      return M.Dst_Address;
   end IPH_Dst_Address;

   procedure Set_IPH_Dst_Address (P : System.Address; V : AIP.M32_T) is
      M : IP_Header with Address => P, Import;
   begin
      M.Dst_Address := V;
   end Set_IPH_Dst_Address;
end AIP.IPH;
