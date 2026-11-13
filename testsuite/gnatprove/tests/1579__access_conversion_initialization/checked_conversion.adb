with Interfaces; use Interfaces;
with SPARK.Conversions.Access_Conversions;

procedure Checked_Conversion with SPARK_Mode is
   type Source is record
      Value : Unsigned_32;
   end record with Relaxed_Initialization, Size => 32, Alignment => 4;
   for Source use record
      Value at 0 range 0 .. 31;
   end record;

   function Is_Initialized (X : Source) return Boolean
   is (X'Initialized)
   with Ghost => Static;

   package Conversion is new
     SPARK.Conversions.Access_Conversions.Access_Constant_Conversions
       (Source, Unsigned_32, Is_Initialized);

   X : aliased Source := (Value => 42);
   Uninitialized : aliased Source;
begin
   declare
      P : constant not null access constant Source := X'Access;
      Y : constant not null access constant Unsigned_32 :=
        Conversion.Convert_Constant_Access (P); -- @PRECONDITION:PASS
   begin
      pragma Assert (Y.all = 42); -- @ASSERT:PASS
   end;
   declare
      P : constant not null access constant Source := Uninitialized'Access;
      Y : constant not null access constant Unsigned_32 :=
        Conversion.Convert_Constant_Access (P); -- @PRECONDITION:FAIL
   begin
      null;
   end;
end Checked_Conversion;
