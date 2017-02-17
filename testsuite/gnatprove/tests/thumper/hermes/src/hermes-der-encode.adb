---------------------------------------------------------------------------
-- FILE    : hermes-der-encode.adb
-- SUBJECT : Body of a package for encoding DER encoded data.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package body Hermes.DER.Encode is

   function Make_Leading_Identifier
     (Tag_Class       : Tag_Class_Type;
      Structured_Flag : Structured_Flag_Type;
      Tag             : Leading_Number_Type) return Octet is

      Tag_Class_Lookup_Table : constant array(Tag_Class_Type) of Octet :=
        (Class_Universal        => 2#0000_0000#,
         Class_Application      => 2#0100_0000#,
         Class_Context_Specific => 2#1000_0000#,
         Class_Private          => 2#1100_0000#);

      Structured_Flag_Lookup_Table : constant array(Structured_Flag_Type) of Octet :=
        (Primitive              => 2#0000_0000#,
         Constructed            => 2#0010_0000#);

      Leading_Number_Lookup_Table : constant array(Leading_Number_Type) of Octet :=
        (Tag_Reserved           =>  0,
         Tag_Boolean            =>  1,
         Tag_Integer            =>  2,
         Tag_Bit_String         =>  3,
         Tag_Octet_String       =>  4,
         Tag_Null               =>  5,
         Tag_Object_Identifier  =>  6,
         Tag_Object_Descriptor  =>  7,
         Tag_Instance_Of        =>  8,
         Tag_External           =>  8,  -- Same as Instance_Of
         Tag_Real               =>  9,
         Tag_Enumerated         => 10,
         Tag_Embedded_PDV       => 11,
         Tag_UTF8_String        => 12,
         Tag_Relative_OID       => 13,
         -- Values 14 .. 15 omitted (not defined?)
         Tag_Sequence           => 16,
         Tag_Sequence_Of        => 16,  -- Same as Sequence
         Tag_Set                => 17,
         Tag_Set_Of             => 17,  -- Same as Set
         Tag_Numeric_String     => 18,
         Tag_Printable_String   => 19,
         Tag_Teletex_String     => 20,
         Tag_T61_String         => 20,  -- Same as Teletex_String
         Tag_Videotex_String    => 21,
         Tag_IA5_String         => 22,
         Tag_UTC_Time           => 23,
         Tag_Generalized_Time   => 24,
         Tag_Graphic_String     => 25,
         Tag_Visible_String     => 26,
         Tag_ISO646_String      => 26,  -- Same as Visible_String
         Tag_General_String     => 27,
         Tag_Universal_String   => 28,
         Tag_Character_String   => 29,
         Tag_BMP_String         => 30,
         Tag_EXTENDED_TAG       => 31);

   begin
      return
        Tag_Class_Lookup_Table(Tag_Class)             or
        Structured_Flag_Lookup_Table(Structured_Flag) or
        Leading_Number_Lookup_Table(Tag);
   end Make_Leading_Identifier;


   function Put_Length_Value(Length : Natural) return Hermes.Octet_Array is
      Result : Hermes.Octet_Array(1..5):= (others => 0);
      Value : Natural;
   begin
      case Length is
         when 0 .. 127 =>
            Value := Length;
            Result(Result'First) := Hermes.Octet(Value);
            return Result(Result'First .. Result'First);

         when 128 .. 2**8 - 1 =>
            Value := Length;
            Result(Result'First) := 2#1000_0001#;
            Result(Result'First + 1) := Hermes.Octet(Value);
            return Result(Result'First .. Result'First + 1);

         when 2**8 .. 2**16 - 1 =>
            Value := Length;
            Result(Result'First) := 2#1000_0010#;
            Result(Result'First + 2) := Hermes.Octet(Value rem 2**8); Value := Value / 2**8;
            Result(Result'FIrst + 1) := Hermes.Octet(Value);
            return Result(Result'First .. Result'First + 2);

         when 2**16 .. 2**24 - 1 =>
            Value := Length;
            Result(Result'First) := 2#1000_0011#;
            Result(Result'First + 3) := Hermes.Octet(Value rem 2**8); Value := Value / 2**8;
            Result(Result'First + 2) := Hermes.Octet(Value rem 2**8); Value := Value / 2**8;
            Result(Result'First + 1) := Hermes.Octet(Value);
            return Result(Result'First .. Result'First + 3);

         when others =>
            Value := Length;
            Result(Result'First) := 2#1000_0100#;
            Result(Result'First + 4) := Hermes.Octet(Value rem 2**8); Value := Value / 2**8;
            Result(Result'First + 3) := Hermes.Octet(Value rem 2**8); Value := Value / 2**8;
            Result(Result'First + 2) := Hermes.Octet(Value rem 2**8); Value := Value / 2**8;
            Result(Result'First + 1) := Hermes.Octet(Value);
            return Result(Result'First .. Result'First + 4);
      end case;
   end Put_Length_Value;


   function Put_Boolean_Value(Value : Boolean) return Hermes.Octet_Array is
      Boolean_Value_Octet : constant Hermes.Octet := (if Value then 2#1111_1111# else 2#0000_0000#);
      Boolean_Octet_Array : constant Hermes.Octet_Array :=
        (Make_Leading_Identifier
           (Tag_Class       => Class_Universal,
            Structured_Flag => Primitive,
            Tag             => Tag_Boolean) & 2#0000_0001# & Boolean_Value_Octet);
   begin
      return Boolean_Octet_Array;
   end Put_Boolean_Value;


   function Put_Integer_Value(Value : Integer) return Hermes.Octet_Array is
      Integer_Octet_Array : Hermes.Octet_Array(1 .. 0);
   begin
      raise Program_Error with "Hermes.DER.Encode.Put_Integer_Value not implemented";
      return Integer_Octet_Array;
   end Put_Integer_Value;


   function Put_Octet_String_Value(Value : Hermes.Octet_Array) return Hermes.Octet_Array is
     (Make_Leading_Identifier
        (Tag_Class       => Class_Universal,
         Structured_Flag => Primitive,
         Tag             => Tag_Octet_String) & Put_Length_Value(Value'Length) & Value);


   function Put_Null_Value return Hermes.Octet_Array is
     (Make_Leading_Identifier
        (Tag_Class       => Class_Universal,
         Structured_Flag => Primitive,
         Tag             => Tag_Null) & 2#0000_0000#);


   function Put_OID_Value(Value : Hermes.OID.Object_Identifier) return Hermes.Octet_Array is
      OID_Octet_Array : Hermes.Octet_Array(1 .. 0);
   begin
      raise Program_Error with "Hermes.DER.Encode.Put_OID_Value not implemented";
      return OID_Octet_Array;
   end Put_OID_Value;

end Hermes.DER.Encode;
