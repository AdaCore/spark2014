--  This file has been automatically generated from src/proto/udph.xml
--  DO NOT EDIT!!!

pragma Warnings (Off);
pragma Style_Checks ("NM32766");
pragma Ada_2012;

with System;

package AIP.UDPH is

   pragma Pure;

   ----------------
   -- UDP_Header --
   ----------------

   type UDP_Header is private;
   UDP_Header_Size : constant := 64;

   function  UDPH_Src_Port     (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_UDPH_Src_Port (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, UDPH_Src_Port, "AIP_UDPH_Src_Port");
   pragma Export (C, Set_UDPH_Src_Port, "AIP_Set_UDPH_Src_Port");

   function  UDPH_Dst_Port     (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_UDPH_Dst_Port (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, UDPH_Dst_Port, "AIP_UDPH_Dst_Port");
   pragma Export (C, Set_UDPH_Dst_Port, "AIP_Set_UDPH_Dst_Port");

   function  UDPH_Length       (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_UDPH_Length   (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, UDPH_Length, "AIP_UDPH_Length");
   pragma Export (C, Set_UDPH_Length, "AIP_Set_UDPH_Length");

   function  UDPH_Checksum     (P : System.Address) return AIP.M16_T
     with Inline;
   procedure Set_UDPH_Checksum (P : System.Address; V : AIP.M16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, UDPH_Checksum, "AIP_UDPH_Checksum");
   pragma Export (C, Set_UDPH_Checksum, "AIP_Set_UDPH_Checksum");

   -----------------------
   -- UDP_Pseudo_Header --
   -----------------------

   type UDP_Pseudo_Header is private;
   UDP_Pseudo_Header_Size : constant := 96;

   function  UDPP_Src_Address     (P : System.Address) return AIP.M32_T
     with Inline;
   procedure Set_UDPP_Src_Address (P : System.Address; V : AIP.M32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, UDPP_Src_Address, "AIP_UDPP_Src_Address");
   pragma Export (C, Set_UDPP_Src_Address, "AIP_Set_UDPP_Src_Address");

   function  UDPP_Dst_Address     (P : System.Address) return AIP.M32_T
     with Inline;
   procedure Set_UDPP_Dst_Address (P : System.Address; V : AIP.M32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, UDPP_Dst_Address, "AIP_UDPP_Dst_Address");
   pragma Export (C, Set_UDPP_Dst_Address, "AIP_Set_UDPP_Dst_Address");

   function  UDPP_Zero            (P : System.Address) return AIP.U8_T
     with Inline;
   procedure Set_UDPP_Zero        (P : System.Address; V : AIP.U8_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, UDPP_Zero, "AIP_UDPP_Zero");
   pragma Export (C, Set_UDPP_Zero, "AIP_Set_UDPP_Zero");

   function  UDPP_Protocol        (P : System.Address) return AIP.U8_T
     with Inline;
   procedure Set_UDPP_Protocol    (P : System.Address; V : AIP.U8_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, UDPP_Protocol, "AIP_UDPP_Protocol");
   pragma Export (C, Set_UDPP_Protocol, "AIP_Set_UDPP_Protocol");

   function  UDPP_Length          (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_UDPP_Length      (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, UDPP_Length, "AIP_UDPP_Length");
   pragma Export (C, Set_UDPP_Length, "AIP_Set_UDPP_Length");

private

   type UDP_Header is record
      Src_Port : AIP.U16_T;
      Dst_Port : AIP.U16_T;
      Length   : AIP.U16_T;
      Checksum : AIP.M16_T;
   end record
   with
     Alignment            => 1,
     Bit_Order            => System.High_Order_First,
     Scalar_Storage_Order => System.High_Order_First;

   for UDP_Header use record
      Src_Port at 0 range 0 .. 15;
      Dst_Port at 0 range 16 .. 31;
      Length   at 4 range 0 .. 15;
      Checksum at 4 range 16 .. 31;
   end record;

   type UDP_Pseudo_Header is record
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

   for UDP_Pseudo_Header use record
      Src_Address at 0 range 0 .. 31;
      Dst_Address at 4 range 0 .. 31;
      Zero        at 8 range 0 .. 7;
      Protocol    at 8 range 8 .. 15;
      Length      at 8 range 16 .. 31;
   end record;
end AIP.UDPH;
