with Ada.Numerics.Big_Numbers.Big_Integers;
with Ada.Numerics.Big_Numbers.Big_Reals;

procedure Big_Literals with SPARK_Mode is
   package BI renames Ada.Numerics.Big_Numbers.Big_Integers;
   package BR renames Ada.Numerics.Big_Numbers.Big_Reals;
   use type BI.Big_Integer;
   use type BR.Big_Real;

   Huge : constant BI.Big_Integer :=
     BI.From_String ("   -12345678901234567890123456789012345678901234567890");
   R : constant BR.Big_Real := BR.From_String ("-12.375");
   S : constant BR.Big_Real := BR.From_String ("-12.375E-2");

   function Cube (Text : String) return BI.Big_Integer is
     (BI.From_String (Text) ** 3); --  @PRECONDITION:FAIL

   procedure Dynamic_Base (Base : BI.Valid_Big_Integer) with
     Pre => Base = BI.To_Big_Integer (2)
   is
   begin
      pragma Assert (Base ** 3 = BI.To_Big_Integer (8));
   end Dynamic_Base;
begin
   pragma Assert
     (Huge = -BI.Big_Integer'(12345678901234567890123456789012345678901234567890));
   pragma Assert (R = -BR.To_Big_Real (99) / BR.To_Big_Real (8));
   pragma Assert (S = -BR.To_Big_Real (99) / BR.To_Big_Real (800));
   Dynamic_Base (BI.To_Big_Integer (2));
end Big_Literals;
