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
