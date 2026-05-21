procedure Bad_Intrinsic with SPARK_Mode is

   type Integer_8 is range -128 .. 127;

   type Unsigned_8 is mod 256;

   function "+" (X : Unsigned_8) return Integer_8 with
     Import, Convention => Intrinsic;

   function "+" (X : Unsigned_8; Y: Integer_8) return Unsigned_8 with
     Import, Convention => Intrinsic;

   function Id (X : Integer_8) return Integer_8 is (X);

   function Id (X : Unsigned_8) return Unsigned_8 is (X);

   procedure Test_Add is
      X : Unsigned_8 := 127;
      Y : Integer_8 := Id (-10);
   begin
      pragma Assert (X + Y = 117); --  This raises Constraint_Error
   end Test_Add;

begin
   Test_Add;
end;
