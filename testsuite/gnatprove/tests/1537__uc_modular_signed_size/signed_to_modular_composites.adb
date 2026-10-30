with Ada.Unchecked_Conversion;

procedure Signed_To_Modular_Composites with SPARK_Mode is
   type S24 is range -(2 ** 23) .. 2 ** 23 - 1 with Size => 24;
   type U24 is mod 2 ** 24 with Size => 24;

   type Modular_Record is record
      Value : U24;
   end record with Size => 24;
   for Modular_Record use record
      Value at 0 range 0 .. 23;
   end record;
   type Modular_Array is array (1 .. 1) of U24
     with Component_Size => 24, Size => 24;

   type Signed_Record is record
      Value : S24;
   end record with Size => 24;
   for Signed_Record use record
      Value at 0 range 0 .. 23;
   end record;
   type Signed_Array is array (1 .. 1) of S24
     with Component_Size => 24, Size => 24;

   function To_Record is new Ada.Unchecked_Conversion (S24, Modular_Record);
   function To_Array is new Ada.Unchecked_Conversion (S24, Modular_Array);
   function From_Record is new Ada.Unchecked_Conversion (Signed_Record, U24);
   function From_Array is new Ada.Unchecked_Conversion (Signed_Array, U24);

   R : Modular_Record;
   A : Modular_Array;
begin
   --  Scalar sources use the actual size when forming the intermediate bits
   R := To_Record (-1);
   pragma Assert (R.Value = 16#FF_FFFF#);
   A := To_Array (-1);
   pragma Assert (A (1) = 16#FF_FFFF#);
   R := To_Record (S24'First);
   pragma Assert (R.Value = 16#80_0000#);
   A := To_Array (S24'First);
   pragma Assert (A (1) = 16#80_0000#);

   --  Composite sources already mask the signed components while packing
   pragma Assert
     (From_Record (Signed_Record'(Value => -1)) = 16#FF_FFFF#);
   pragma Assert
     (From_Array (Signed_Array'(1 => -1)) = 16#FF_FFFF#);
   pragma Assert
     (From_Record (Signed_Record'(Value => S24'First)) = 16#80_0000#);
   pragma Assert
     (From_Array (Signed_Array'(1 => S24'First)) = 16#80_0000#);
end Signed_To_Modular_Composites;
