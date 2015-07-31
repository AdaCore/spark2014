--  This file has been automatically generated from src/proto/arph.xml
--  DO NOT EDIT!!!

pragma Warnings (Off);
pragma Style_Checks ("NM32766");
pragma Ada_2012;

with System;

package AIP.ARPH is

   pragma Pure;

   ------------
   -- ARP_Hw --
   ------------

   ARP_Hw_Ethernet : constant := 1;

   ------------
   -- ARP_Op --
   ------------

   ARP_Op_Request : constant := 1;
   ARP_Op_Reply   : constant := 2;

   ----------------
   -- ARP_Header --
   ----------------

   type ARP_Header is private;
   ARP_Header_Size : constant := 224;

   function  ARPH_Hardware_Type       (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_ARPH_Hardware_Type   (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ARPH_Hardware_Type, "AIP_ARPH_Hardware_Type");
   pragma Export (C, Set_ARPH_Hardware_Type, "AIP_Set_ARPH_Hardware_Type");

   function  ARPH_Protocol            (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_ARPH_Protocol        (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ARPH_Protocol, "AIP_ARPH_Protocol");
   pragma Export (C, Set_ARPH_Protocol, "AIP_Set_ARPH_Protocol");

   function  ARPH_Hw_Len              (P : System.Address) return AIP.U8_T
     with Inline;
   procedure Set_ARPH_Hw_Len          (P : System.Address; V : AIP.U8_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ARPH_Hw_Len, "AIP_ARPH_Hw_Len");
   pragma Export (C, Set_ARPH_Hw_Len, "AIP_Set_ARPH_Hw_Len");

   function  ARPH_Pr_Len              (P : System.Address) return AIP.U8_T
     with Inline;
   procedure Set_ARPH_Pr_Len          (P : System.Address; V : AIP.U8_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ARPH_Pr_Len, "AIP_ARPH_Pr_Len");
   pragma Export (C, Set_ARPH_Pr_Len, "AIP_Set_ARPH_Pr_Len");

   function  ARPH_Operation           (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_ARPH_Operation       (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ARPH_Operation, "AIP_ARPH_Operation");
   pragma Export (C, Set_ARPH_Operation, "AIP_Set_ARPH_Operation");

   function  ARPH_Src_Eth_Address     (P : System.Address) return AIP.Ethernet_Address
     with Inline;
   procedure Set_ARPH_Src_Eth_Address (P : System.Address; V : AIP.Ethernet_Address)
     with Inline, Depends => (null => (P, V));

   function  ARPH_Src_IP_Address      (P : System.Address) return AIP.M32_T
     with Inline;
   procedure Set_ARPH_Src_IP_Address  (P : System.Address; V : AIP.M32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ARPH_Src_IP_Address, "AIP_ARPH_Src_IP_Address");
   pragma Export (C, Set_ARPH_Src_IP_Address, "AIP_Set_ARPH_Src_IP_Address");

   function  ARPH_Dst_Eth_Address     (P : System.Address) return AIP.Ethernet_Address
     with Inline;
   procedure Set_ARPH_Dst_Eth_Address (P : System.Address; V : AIP.Ethernet_Address)
     with Inline, Depends => (null => (P, V));

   function  ARPH_Dst_IP_Address      (P : System.Address) return AIP.M32_T
     with Inline;
   procedure Set_ARPH_Dst_IP_Address  (P : System.Address; V : AIP.M32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ARPH_Dst_IP_Address, "AIP_ARPH_Dst_IP_Address");
   pragma Export (C, Set_ARPH_Dst_IP_Address, "AIP_Set_ARPH_Dst_IP_Address");

private

   type ARP_Header is record
      Hardware_Type   : AIP.U16_T;
      Protocol        : AIP.U16_T;
      Hw_Len          : AIP.U8_T;
      Pr_Len          : AIP.U8_T;
      Operation       : AIP.U16_T;
      Src_Eth_Address : AIP.Ethernet_Address;
      Src_IP_Address  : AIP.M32_T;
      Dst_Eth_Address : AIP.Ethernet_Address;
      Dst_IP_Address  : AIP.M32_T;
   end record
   with
     Alignment            => 1,
     Bit_Order            => System.High_Order_First,
     Scalar_Storage_Order => System.High_Order_First;

   for ARP_Header use record
      Hardware_Type   at 0 range 0 .. 15;
      Protocol        at 0 range 16 .. 31;
      Hw_Len          at 4 range 0 .. 7;
      Pr_Len          at 4 range 8 .. 15;
      Operation       at 4 range 16 .. 31;
      Src_Eth_Address at 8 range 0 .. 47;
      Src_IP_Address  at 12 range 16 .. 47;
      Dst_Eth_Address at 16 range 16 .. 63;
      Dst_IP_Address  at 24 range 0 .. 31;
   end record;
end AIP.ARPH;
--  This file has been automatically generated from src/proto/arph.xml
--  DO NOT EDIT!!!

pragma Warnings (Off);
pragma Style_Checks ("NM32766");
pragma Ada_2012;

package body AIP.ARPH with
  SPARK_Mode => Off
is

   function  ARPH_Hardware_Type       (P : System.Address) return AIP.U16_T is
      M : ARP_Header with Address => P, Import;
   begin
      return M.Hardware_Type;
   end ARPH_Hardware_Type;

   procedure Set_ARPH_Hardware_Type   (P : System.Address; V : AIP.U16_T) is
      M : ARP_Header with Address => P, Import;
   begin
      M.Hardware_Type := V;
   end Set_ARPH_Hardware_Type;

   function  ARPH_Protocol            (P : System.Address) return AIP.U16_T is
      M : ARP_Header with Address => P, Import;
   begin
      return M.Protocol;
   end ARPH_Protocol;

   procedure Set_ARPH_Protocol        (P : System.Address; V : AIP.U16_T) is
      M : ARP_Header with Address => P, Import;
   begin
      M.Protocol := V;
   end Set_ARPH_Protocol;

   function  ARPH_Hw_Len              (P : System.Address) return AIP.U8_T is
      M : ARP_Header with Address => P, Import;
   begin
      return M.Hw_Len;
   end ARPH_Hw_Len;

   procedure Set_ARPH_Hw_Len          (P : System.Address; V : AIP.U8_T) is
      M : ARP_Header with Address => P, Import;
   begin
      M.Hw_Len := V;
   end Set_ARPH_Hw_Len;

   function  ARPH_Pr_Len              (P : System.Address) return AIP.U8_T is
      M : ARP_Header with Address => P, Import;
   begin
      return M.Pr_Len;
   end ARPH_Pr_Len;

   procedure Set_ARPH_Pr_Len          (P : System.Address; V : AIP.U8_T) is
      M : ARP_Header with Address => P, Import;
   begin
      M.Pr_Len := V;
   end Set_ARPH_Pr_Len;

   function  ARPH_Operation           (P : System.Address) return AIP.U16_T is
      M : ARP_Header with Address => P, Import;
   begin
      return M.Operation;
   end ARPH_Operation;

   procedure Set_ARPH_Operation       (P : System.Address; V : AIP.U16_T) is
      M : ARP_Header with Address => P, Import;
   begin
      M.Operation := V;
   end Set_ARPH_Operation;

   function  ARPH_Src_Eth_Address     (P : System.Address) return AIP.Ethernet_Address is
      M : ARP_Header with Address => P, Import;
   begin
      return M.Src_Eth_Address;
   end ARPH_Src_Eth_Address;

   procedure Set_ARPH_Src_Eth_Address (P : System.Address; V : AIP.Ethernet_Address) is
      M : ARP_Header with Address => P, Import;
   begin
      M.Src_Eth_Address := V;
   end Set_ARPH_Src_Eth_Address;

   function  ARPH_Src_IP_Address      (P : System.Address) return AIP.M32_T is
      M : ARP_Header with Address => P, Import;
   begin
      return M.Src_IP_Address;
   end ARPH_Src_IP_Address;

   procedure Set_ARPH_Src_IP_Address  (P : System.Address; V : AIP.M32_T) is
      M : ARP_Header with Address => P, Import;
   begin
      M.Src_IP_Address := V;
   end Set_ARPH_Src_IP_Address;

   function  ARPH_Dst_Eth_Address     (P : System.Address) return AIP.Ethernet_Address is
      M : ARP_Header with Address => P, Import;
   begin
      return M.Dst_Eth_Address;
   end ARPH_Dst_Eth_Address;

   procedure Set_ARPH_Dst_Eth_Address (P : System.Address; V : AIP.Ethernet_Address) is
      M : ARP_Header with Address => P, Import;
   begin
      M.Dst_Eth_Address := V;
   end Set_ARPH_Dst_Eth_Address;

   function  ARPH_Dst_IP_Address      (P : System.Address) return AIP.M32_T is
      M : ARP_Header with Address => P, Import;
   begin
      return M.Dst_IP_Address;
   end ARPH_Dst_IP_Address;

   procedure Set_ARPH_Dst_IP_Address  (P : System.Address; V : AIP.M32_T) is
      M : ARP_Header with Address => P, Import;
   begin
      M.Dst_IP_Address := V;
   end Set_ARPH_Dst_IP_Address;
end AIP.ARPH;
