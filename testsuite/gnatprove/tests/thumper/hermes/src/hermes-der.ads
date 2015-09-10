---------------------------------------------------------------------------
-- FILE    : hermes-der.ads
-- SUBJECT : Specification of a package for handling the distinguished encoding rules.
-- AUTHOR  : (C) Copyright 2015 by Peter Chapin
--
-- Please send comments or bug reports to
--
--      Peter Chapin <PChapin@vtc.vsc.edu>
---------------------------------------------------------------------------
pragma SPARK_Mode(On);

package Hermes.DER is

   -- Used to indicate the success or value of the subprograms in this package.
   type Status_Type is
     (Success,
      Bad_Identifier,
      Indefinite_Length,
      Unimplemented_Length,
      Bad_Length,
      Unimplemented_Value,
      Bad_Value);

   type Tag_Class_Type is
     (Class_Universal, Class_Application, Class_Context_Specific, Class_Private);

   type Structured_Flag_Type is (Primitive, Constructed);

   type Leading_Number_Type is
     (Tag_Reserved,
      Tag_Boolean,
      Tag_Integer,
      Tag_Bit_String,
      Tag_Octet_String,
      Tag_Null,
      Tag_Object_Identifier,
      Tag_Object_Descriptor,
      Tag_Instance_Of,
      Tag_External,
      Tag_Real,
      Tag_Enumerated,
      Tag_Embedded_PDV,
      Tag_UTF8_String,
      Tag_Relative_OID,
      Tag_Sequence,
      Tag_Sequence_Of,
      Tag_Set,
      Tag_Set_Of,
      Tag_Numeric_String,
      Tag_Printable_String,
      Tag_Teletex_String,
      Tag_T61_String,
      Tag_Videotex_String,
      Tag_IA5_String,
      Tag_UTC_Time,
      Tag_Generalized_Time,
      Tag_Graphic_String,
      Tag_Visible_String,
      Tag_ISO646_String,
      Tag_General_String,
      Tag_Universal_String,
      Tag_Character_String,
      Tag_BMP_String,
      Tag_EXTENDED_TAG);

end Hermes.DER;
