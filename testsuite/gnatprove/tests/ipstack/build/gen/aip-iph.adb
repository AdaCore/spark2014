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
