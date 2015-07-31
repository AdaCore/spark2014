--  This file has been automatically generated from src/proto/etherh.xml
--  DO NOT EDIT!!!

pragma Warnings (Off);
pragma Style_Checks ("NM32766");
pragma Ada_2012;

package body AIP.EtherH with
  SPARK_Mode => Off
is

   function  EtherH_Dst_MAC_Address     (P : System.Address) return AIP.Ethernet_Address is
      M : Ether_Header with Address => P, Import;
   begin
      return M.Dst_MAC_Address;
   end EtherH_Dst_MAC_Address;

   procedure Set_EtherH_Dst_MAC_Address (P : System.Address; V : AIP.Ethernet_Address) is
      M : Ether_Header with Address => P, Import;
   begin
      M.Dst_MAC_Address := V;
   end Set_EtherH_Dst_MAC_Address;

   function  EtherH_Src_MAC_Address     (P : System.Address) return AIP.Ethernet_Address is
      M : Ether_Header with Address => P, Import;
   begin
      return M.Src_MAC_Address;
   end EtherH_Src_MAC_Address;

   procedure Set_EtherH_Src_MAC_Address (P : System.Address; V : AIP.Ethernet_Address) is
      M : Ether_Header with Address => P, Import;
   begin
      M.Src_MAC_Address := V;
   end Set_EtherH_Src_MAC_Address;

   function  EtherH_Frame_Type          (P : System.Address) return AIP.U16_T is
      M : Ether_Header with Address => P, Import;
   begin
      return M.Frame_Type;
   end EtherH_Frame_Type;

   procedure Set_EtherH_Frame_Type      (P : System.Address; V : AIP.U16_T) is
      M : Ether_Header with Address => P, Import;
   begin
      M.Frame_Type := V;
   end Set_EtherH_Frame_Type;
end AIP.EtherH;
