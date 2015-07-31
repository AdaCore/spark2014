--  This file has been automatically generated from src/proto/etherh.xml
--  DO NOT EDIT!!!

pragma Warnings (Off);
pragma Style_Checks ("NM32766");
pragma Ada_2012;

with System;

package AIP.EtherH is

   pragma Pure;

   ----------------
   -- Ether_Type --
   ----------------

   Ether_Type_ARP        : constant := 16#806#;
   Ether_Type_IP         : constant := 16#800#;
   Ether_Type_PPPoE_Disc : constant := 16#8863#;
   Ether_Type_PPPoE      : constant := 16#8864#;

   ------------------
   -- Ether_Header --
   ------------------

   type Ether_Header is private;
   Ether_Header_Size : constant := 112;

   function  EtherH_Dst_MAC_Address     (P : System.Address) return AIP.Ethernet_Address
     with Inline;
   procedure Set_EtherH_Dst_MAC_Address (P : System.Address; V : AIP.Ethernet_Address)
     with Inline, Depends => (null => (P, V));

   function  EtherH_Src_MAC_Address     (P : System.Address) return AIP.Ethernet_Address
     with Inline;
   procedure Set_EtherH_Src_MAC_Address (P : System.Address; V : AIP.Ethernet_Address)
     with Inline, Depends => (null => (P, V));

   function  EtherH_Frame_Type          (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_EtherH_Frame_Type      (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, EtherH_Frame_Type, "AIP_EtherH_Frame_Type");
   pragma Export (C, Set_EtherH_Frame_Type, "AIP_Set_EtherH_Frame_Type");

private

   type Ether_Header is record
      Dst_MAC_Address : AIP.Ethernet_Address;
      Src_MAC_Address : AIP.Ethernet_Address;
      Frame_Type      : AIP.U16_T;
   end record
   with
     Alignment            => 1,
     Bit_Order            => System.High_Order_First,
     Scalar_Storage_Order => System.High_Order_First;

   for Ether_Header use record
      Dst_MAC_Address at 0 range 0 .. 47;
      Src_MAC_Address at 4 range 16 .. 63;
      Frame_Type      at 12 range 0 .. 15;
   end record;
end AIP.EtherH;
