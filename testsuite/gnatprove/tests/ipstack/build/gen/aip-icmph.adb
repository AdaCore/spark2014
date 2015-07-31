--  This file has been automatically generated from src/proto/icmph.xml
--  DO NOT EDIT!!!

pragma Warnings (Off);
pragma Style_Checks ("NM32766");
pragma Ada_2012;

package body AIP.ICMPH with
  SPARK_Mode => Off
is

   function  ICMPH_I_Type       (P : System.Address) return AIP.U8_T is
      M : ICMP_Header with Address => P, Import;
   begin
      return M.I_Type;
   end ICMPH_I_Type;

   procedure Set_ICMPH_I_Type   (P : System.Address; V : AIP.U8_T) is
      M : ICMP_Header with Address => P, Import;
   begin
      M.I_Type := V;
   end Set_ICMPH_I_Type;

   function  ICMPH_Code         (P : System.Address) return AIP.U8_T is
      M : ICMP_Header with Address => P, Import;
   begin
      return M.Code;
   end ICMPH_Code;

   procedure Set_ICMPH_Code     (P : System.Address; V : AIP.U8_T) is
      M : ICMP_Header with Address => P, Import;
   begin
      M.Code := V;
   end Set_ICMPH_Code;

   function  ICMPH_Checksum     (P : System.Address) return AIP.M16_T is
      M : ICMP_Header with Address => P, Import;
   begin
      return M.Checksum;
   end ICMPH_Checksum;

   procedure Set_ICMPH_Checksum (P : System.Address; V : AIP.M16_T) is
      M : ICMP_Header with Address => P, Import;
   begin
      M.Checksum := V;
   end Set_ICMPH_Checksum;

   function  ICMP_TSH_ICMPH          (P : System.Address) return AIP.U32_T is
      M : ICMP_Timestamp_Header with Address => P, Import;
   begin
      return M.ICMPH;
   end ICMP_TSH_ICMPH;

   procedure Set_ICMP_TSH_ICMPH      (P : System.Address; V : AIP.U32_T) is
      M : ICMP_Timestamp_Header with Address => P, Import;
   begin
      M.ICMPH := V;
   end Set_ICMP_TSH_ICMPH;

   function  ICMP_TSH_Identifier     (P : System.Address) return AIP.U16_T is
      M : ICMP_Timestamp_Header with Address => P, Import;
   begin
      return M.Identifier;
   end ICMP_TSH_Identifier;

   procedure Set_ICMP_TSH_Identifier (P : System.Address; V : AIP.U16_T) is
      M : ICMP_Timestamp_Header with Address => P, Import;
   begin
      M.Identifier := V;
   end Set_ICMP_TSH_Identifier;

   function  ICMP_TSH_Sequence       (P : System.Address) return AIP.U16_T is
      M : ICMP_Timestamp_Header with Address => P, Import;
   begin
      return M.Sequence;
   end ICMP_TSH_Sequence;

   procedure Set_ICMP_TSH_Sequence   (P : System.Address; V : AIP.U16_T) is
      M : ICMP_Timestamp_Header with Address => P, Import;
   begin
      M.Sequence := V;
   end Set_ICMP_TSH_Sequence;

   function  ICMP_TSH_Originate      (P : System.Address) return AIP.U32_T is
      M : ICMP_Timestamp_Header with Address => P, Import;
   begin
      return M.Originate;
   end ICMP_TSH_Originate;

   procedure Set_ICMP_TSH_Originate  (P : System.Address; V : AIP.U32_T) is
      M : ICMP_Timestamp_Header with Address => P, Import;
   begin
      M.Originate := V;
   end Set_ICMP_TSH_Originate;

   function  ICMP_TSH_Receive        (P : System.Address) return AIP.U32_T is
      M : ICMP_Timestamp_Header with Address => P, Import;
   begin
      return M.Receive;
   end ICMP_TSH_Receive;

   procedure Set_ICMP_TSH_Receive    (P : System.Address; V : AIP.U32_T) is
      M : ICMP_Timestamp_Header with Address => P, Import;
   begin
      M.Receive := V;
   end Set_ICMP_TSH_Receive;

   function  ICMP_TSH_Transmit       (P : System.Address) return AIP.U32_T is
      M : ICMP_Timestamp_Header with Address => P, Import;
   begin
      return M.Transmit;
   end ICMP_TSH_Transmit;

   procedure Set_ICMP_TSH_Transmit   (P : System.Address; V : AIP.U32_T) is
      M : ICMP_Timestamp_Header with Address => P, Import;
   begin
      M.Transmit := V;
   end Set_ICMP_TSH_Transmit;

   function  ICMP_RH_ICMPH               (P : System.Address) return AIP.U32_T is
      M : ICMP_Redirect_Header with Address => P, Import;
   begin
      return M.ICMPH;
   end ICMP_RH_ICMPH;

   procedure Set_ICMP_RH_ICMPH           (P : System.Address; V : AIP.U32_T) is
      M : ICMP_Redirect_Header with Address => P, Import;
   begin
      M.ICMPH := V;
   end Set_ICMP_RH_ICMPH;

   function  ICMP_RH_Gateway_Address     (P : System.Address) return AIP.U32_T is
      M : ICMP_Redirect_Header with Address => P, Import;
   begin
      return M.Gateway_Address;
   end ICMP_RH_Gateway_Address;

   procedure Set_ICMP_RH_Gateway_Address (P : System.Address; V : AIP.U32_T) is
      M : ICMP_Redirect_Header with Address => P, Import;
   begin
      M.Gateway_Address := V;
   end Set_ICMP_RH_Gateway_Address;

   function  ICMP_Generic_H_ICMPH       (P : System.Address) return AIP.U32_T is
      M : ICMP_Generic_Header with Address => P, Import;
   begin
      return M.ICMPH;
   end ICMP_Generic_H_ICMPH;

   procedure Set_ICMP_Generic_H_ICMPH   (P : System.Address; V : AIP.U32_T) is
      M : ICMP_Generic_Header with Address => P, Import;
   begin
      M.ICMPH := V;
   end Set_ICMP_Generic_H_ICMPH;

   function  ICMP_Generic_H_Pointer     (P : System.Address) return AIP.U8_T is
      M : ICMP_Generic_Header with Address => P, Import;
   begin
      return M.Pointer;
   end ICMP_Generic_H_Pointer;

   procedure Set_ICMP_Generic_H_Pointer (P : System.Address; V : AIP.U8_T) is
      M : ICMP_Generic_Header with Address => P, Import;
   begin
      M.Pointer := V;
   end Set_ICMP_Generic_H_Pointer;

   function  ICMP_Generic_H_Unused      (P : System.Address) return AIP.U24_T is
      M : ICMP_Generic_Header with Address => P, Import;
   begin
      return M.Unused;
   end ICMP_Generic_H_Unused;

   procedure Set_ICMP_Generic_H_Unused  (P : System.Address; V : AIP.U24_T) is
      M : ICMP_Generic_Header with Address => P, Import;
   begin
      M.Unused := V;
   end Set_ICMP_Generic_H_Unused;
end AIP.ICMPH;
