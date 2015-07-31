--  This file has been automatically generated from src/proto/udph.xml
--  DO NOT EDIT!!!

pragma Warnings (Off);
pragma Style_Checks ("NM32766");
pragma Ada_2012;

package body AIP.UDPH with
  SPARK_Mode => Off
is

   function  UDPH_Src_Port     (P : System.Address) return AIP.U16_T is
      M : UDP_Header with Address => P, Import;
   begin
      return M.Src_Port;
   end UDPH_Src_Port;

   procedure Set_UDPH_Src_Port (P : System.Address; V : AIP.U16_T) is
      M : UDP_Header with Address => P, Import;
   begin
      M.Src_Port := V;
   end Set_UDPH_Src_Port;

   function  UDPH_Dst_Port     (P : System.Address) return AIP.U16_T is
      M : UDP_Header with Address => P, Import;
   begin
      return M.Dst_Port;
   end UDPH_Dst_Port;

   procedure Set_UDPH_Dst_Port (P : System.Address; V : AIP.U16_T) is
      M : UDP_Header with Address => P, Import;
   begin
      M.Dst_Port := V;
   end Set_UDPH_Dst_Port;

   function  UDPH_Length       (P : System.Address) return AIP.U16_T is
      M : UDP_Header with Address => P, Import;
   begin
      return M.Length;
   end UDPH_Length;

   procedure Set_UDPH_Length   (P : System.Address; V : AIP.U16_T) is
      M : UDP_Header with Address => P, Import;
   begin
      M.Length := V;
   end Set_UDPH_Length;

   function  UDPH_Checksum     (P : System.Address) return AIP.M16_T is
      M : UDP_Header with Address => P, Import;
   begin
      return M.Checksum;
   end UDPH_Checksum;

   procedure Set_UDPH_Checksum (P : System.Address; V : AIP.M16_T) is
      M : UDP_Header with Address => P, Import;
   begin
      M.Checksum := V;
   end Set_UDPH_Checksum;

   function  UDPP_Src_Address     (P : System.Address) return AIP.M32_T is
      M : UDP_Pseudo_Header with Address => P, Import;
   begin
      return M.Src_Address;
   end UDPP_Src_Address;

   procedure Set_UDPP_Src_Address (P : System.Address; V : AIP.M32_T) is
      M : UDP_Pseudo_Header with Address => P, Import;
   begin
      M.Src_Address := V;
   end Set_UDPP_Src_Address;

   function  UDPP_Dst_Address     (P : System.Address) return AIP.M32_T is
      M : UDP_Pseudo_Header with Address => P, Import;
   begin
      return M.Dst_Address;
   end UDPP_Dst_Address;

   procedure Set_UDPP_Dst_Address (P : System.Address; V : AIP.M32_T) is
      M : UDP_Pseudo_Header with Address => P, Import;
   begin
      M.Dst_Address := V;
   end Set_UDPP_Dst_Address;

   function  UDPP_Zero            (P : System.Address) return AIP.U8_T is
      M : UDP_Pseudo_Header with Address => P, Import;
   begin
      return M.Zero;
   end UDPP_Zero;

   procedure Set_UDPP_Zero        (P : System.Address; V : AIP.U8_T) is
      M : UDP_Pseudo_Header with Address => P, Import;
   begin
      M.Zero := V;
   end Set_UDPP_Zero;

   function  UDPP_Protocol        (P : System.Address) return AIP.U8_T is
      M : UDP_Pseudo_Header with Address => P, Import;
   begin
      return M.Protocol;
   end UDPP_Protocol;

   procedure Set_UDPP_Protocol    (P : System.Address; V : AIP.U8_T) is
      M : UDP_Pseudo_Header with Address => P, Import;
   begin
      M.Protocol := V;
   end Set_UDPP_Protocol;

   function  UDPP_Length          (P : System.Address) return AIP.U16_T is
      M : UDP_Pseudo_Header with Address => P, Import;
   begin
      return M.Length;
   end UDPP_Length;

   procedure Set_UDPP_Length      (P : System.Address; V : AIP.U16_T) is
      M : UDP_Pseudo_Header with Address => P, Import;
   begin
      M.Length := V;
   end Set_UDPP_Length;
end AIP.UDPH;
