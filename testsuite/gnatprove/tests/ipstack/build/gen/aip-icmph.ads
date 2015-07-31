--  This file has been automatically generated from src/proto/icmph.xml
--  DO NOT EDIT!!!

pragma Warnings (Off);
pragma Style_Checks ("NM32766");
pragma Ada_2012;

with System;
with AIP.IPH;

package AIP.ICMPH is

   pragma Pure;

   ---------------
   -- ICMP_Type --
   ---------------

   ICMP_Type_Echo_Reply        : constant := 0;
   ICMP_Type_Dest_Unreachable  : constant := 3;
   ICMP_Type_Source_Quench     : constant := 4;
   ICMP_Type_Redirect          : constant := 5;
   ICMP_Type_Echo              : constant := 8;
   ICMP_Type_Time_Exceeded     : constant := 11;
   ICMP_Type_Parameter_Problem : constant := 12;
   ICMP_Type_Timestamp         : constant := 13;
   ICMP_Type_Timestamp_Reply   : constant := 14;
   ICMP_Type_Info_Request      : constant := 15;
   ICMP_Type_Info_Reply        : constant := 16;

   -----------------------
   -- ICMP_Unreach_Code --
   -----------------------

   ICMP_Unreach_Code_Net_Unreachable   : constant := 0;
   ICMP_Unreach_Code_Host_Unreachable  : constant := 1;
   ICMP_Unreach_Code_Proto_Unreachable : constant := 2;
   ICMP_Unreach_Code_Port_Unreachable  : constant := 3;
   ICMP_Unreach_Code_Must_Fragment     : constant := 4;
   ICMP_Unreach_Code_Src_Route_Failed  : constant := 5;

   ------------------------
   -- ICMP_Redirect_Code --
   ------------------------

   ICMP_Redirect_Code_Redirect_Net      : constant := 0;
   ICMP_Redirect_Code_Redirect_Host     : constant := 1;
   ICMP_Redirect_Code_Redirect_TOS_Net  : constant := 2;
   ICMP_Redirect_Code_Redirect_TOS_Host : constant := 3;

   -----------------
   -- ICMP_Header --
   -----------------

   type ICMP_Header is private;
   ICMP_Header_Size : constant := 32;

   function  ICMPH_I_Type       (P : System.Address) return AIP.U8_T
     with Inline;
   procedure Set_ICMPH_I_Type   (P : System.Address; V : AIP.U8_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ICMPH_I_Type, "AIP_ICMPH_I_Type");
   pragma Export (C, Set_ICMPH_I_Type, "AIP_Set_ICMPH_I_Type");

   function  ICMPH_Code         (P : System.Address) return AIP.U8_T
     with Inline;
   procedure Set_ICMPH_Code     (P : System.Address; V : AIP.U8_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ICMPH_Code, "AIP_ICMPH_Code");
   pragma Export (C, Set_ICMPH_Code, "AIP_Set_ICMPH_Code");

   function  ICMPH_Checksum     (P : System.Address) return AIP.M16_T
     with Inline;
   procedure Set_ICMPH_Checksum (P : System.Address; V : AIP.M16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ICMPH_Checksum, "AIP_ICMPH_Checksum");
   pragma Export (C, Set_ICMPH_Checksum, "AIP_Set_ICMPH_Checksum");

   ---------------------------
   -- ICMP_Timestamp_Header --
   ---------------------------

   type ICMP_Timestamp_Header is private;
   ICMP_Timestamp_Header_Size : constant := 160;

   function  ICMP_TSH_ICMPH          (P : System.Address) return AIP.U32_T
     with Inline;
   procedure Set_ICMP_TSH_ICMPH      (P : System.Address; V : AIP.U32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ICMP_TSH_ICMPH, "AIP_ICMP_TSH_ICMPH");
   pragma Export (C, Set_ICMP_TSH_ICMPH, "AIP_Set_ICMP_TSH_ICMPH");

   function  ICMP_TSH_Identifier     (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_ICMP_TSH_Identifier (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ICMP_TSH_Identifier, "AIP_ICMP_TSH_Identifier");
   pragma Export (C, Set_ICMP_TSH_Identifier, "AIP_Set_ICMP_TSH_Identifier");

   function  ICMP_TSH_Sequence       (P : System.Address) return AIP.U16_T
     with Inline;
   procedure Set_ICMP_TSH_Sequence   (P : System.Address; V : AIP.U16_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ICMP_TSH_Sequence, "AIP_ICMP_TSH_Sequence");
   pragma Export (C, Set_ICMP_TSH_Sequence, "AIP_Set_ICMP_TSH_Sequence");

   function  ICMP_TSH_Originate      (P : System.Address) return AIP.U32_T
     with Inline;
   procedure Set_ICMP_TSH_Originate  (P : System.Address; V : AIP.U32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ICMP_TSH_Originate, "AIP_ICMP_TSH_Originate");
   pragma Export (C, Set_ICMP_TSH_Originate, "AIP_Set_ICMP_TSH_Originate");

   function  ICMP_TSH_Receive        (P : System.Address) return AIP.U32_T
     with Inline;
   procedure Set_ICMP_TSH_Receive    (P : System.Address; V : AIP.U32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ICMP_TSH_Receive, "AIP_ICMP_TSH_Receive");
   pragma Export (C, Set_ICMP_TSH_Receive, "AIP_Set_ICMP_TSH_Receive");

   function  ICMP_TSH_Transmit       (P : System.Address) return AIP.U32_T
     with Inline;
   procedure Set_ICMP_TSH_Transmit   (P : System.Address; V : AIP.U32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ICMP_TSH_Transmit, "AIP_ICMP_TSH_Transmit");
   pragma Export (C, Set_ICMP_TSH_Transmit, "AIP_Set_ICMP_TSH_Transmit");

   --------------------------
   -- ICMP_Redirect_Header --
   --------------------------

   type ICMP_Redirect_Header is private;
   ICMP_Redirect_Header_Size : constant := 64;

   function  ICMP_RH_ICMPH               (P : System.Address) return AIP.U32_T
     with Inline;
   procedure Set_ICMP_RH_ICMPH           (P : System.Address; V : AIP.U32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ICMP_RH_ICMPH, "AIP_ICMP_RH_ICMPH");
   pragma Export (C, Set_ICMP_RH_ICMPH, "AIP_Set_ICMP_RH_ICMPH");

   function  ICMP_RH_Gateway_Address     (P : System.Address) return AIP.U32_T
     with Inline;
   procedure Set_ICMP_RH_Gateway_Address (P : System.Address; V : AIP.U32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ICMP_RH_Gateway_Address, "AIP_ICMP_RH_Gateway_Address");
   pragma Export (C, Set_ICMP_RH_Gateway_Address, "AIP_Set_ICMP_RH_Gateway_Address");

   -------------------------
   -- ICMP_Generic_Header --
   -------------------------

   type ICMP_Generic_Header is private;
   ICMP_Generic_Header_Size : constant := 64;

   function  ICMP_Generic_H_ICMPH       (P : System.Address) return AIP.U32_T
     with Inline;
   procedure Set_ICMP_Generic_H_ICMPH   (P : System.Address; V : AIP.U32_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ICMP_Generic_H_ICMPH, "AIP_ICMP_Generic_H_ICMPH");
   pragma Export (C, Set_ICMP_Generic_H_ICMPH, "AIP_Set_ICMP_Generic_H_ICMPH");

   function  ICMP_Generic_H_Pointer     (P : System.Address) return AIP.U8_T
     with Inline;
   procedure Set_ICMP_Generic_H_Pointer (P : System.Address; V : AIP.U8_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ICMP_Generic_H_Pointer, "AIP_ICMP_Generic_H_Pointer");
   pragma Export (C, Set_ICMP_Generic_H_Pointer, "AIP_Set_ICMP_Generic_H_Pointer");

   function  ICMP_Generic_H_Unused      (P : System.Address) return AIP.U24_T
     with Inline;
   procedure Set_ICMP_Generic_H_Unused  (P : System.Address; V : AIP.U24_T)
     with Inline, Depends => (null => (P, V));
   pragma Export (C, ICMP_Generic_H_Unused, "AIP_ICMP_Generic_H_Unused");
   pragma Export (C, Set_ICMP_Generic_H_Unused, "AIP_Set_ICMP_Generic_H_Unused");

private

   type ICMP_Header is record
      I_Type   : AIP.U8_T;
      Code     : AIP.U8_T;
      Checksum : AIP.M16_T;
   end record
   with
     Alignment            => 1,
     Bit_Order            => System.High_Order_First,
     Scalar_Storage_Order => System.High_Order_First;

   for ICMP_Header use record
      I_Type   at 0 range 0 .. 7;
      Code     at 0 range 8 .. 15;
      Checksum at 0 range 16 .. 31;
   end record;

   type ICMP_Timestamp_Header is record
      ICMPH      : AIP.U32_T;
      Identifier : AIP.U16_T;
      Sequence   : AIP.U16_T;
      Originate  : AIP.U32_T;
      Receive    : AIP.U32_T;
      Transmit   : AIP.U32_T;
   end record
   with
     Alignment            => 1,
     Bit_Order            => System.High_Order_First,
     Scalar_Storage_Order => System.High_Order_First;

   for ICMP_Timestamp_Header use record
      ICMPH      at 0 range 0 .. 31;
      Identifier at 4 range 0 .. 15;
      Sequence   at 4 range 16 .. 31;
      Originate  at 8 range 0 .. 31;
      Receive    at 12 range 0 .. 31;
      Transmit   at 16 range 0 .. 31;
   end record;

   type ICMP_Redirect_Header is record
      ICMPH           : AIP.U32_T;
      Gateway_Address : AIP.U32_T;
   end record
   with
     Alignment            => 1,
     Bit_Order            => System.High_Order_First,
     Scalar_Storage_Order => System.High_Order_First;

   for ICMP_Redirect_Header use record
      ICMPH           at 0 range 0 .. 31;
      Gateway_Address at 4 range 0 .. 31;
   end record;

   type ICMP_Generic_Header is record
      ICMPH   : AIP.U32_T;
      Pointer : AIP.U8_T;
      Unused  : AIP.U24_T;
   end record
   with
     Alignment            => 1,
     Bit_Order            => System.High_Order_First,
     Scalar_Storage_Order => System.High_Order_First;

   for ICMP_Generic_Header use record
      ICMPH   at 0 range 0 .. 31;
      Pointer at 4 range 0 .. 7;
      Unused  at 4 range 8 .. 31;
   end record;
end AIP.ICMPH;
