procedure Very_Bad_Intrinsic with SPARK_Mode is

   type Integer_8 is range -128 .. 127;
   type Unsigned_8 is mod 256;

   function Id (X : Integer_8) return Integer_8 is (X);
   function Id (X : Unsigned_8) return Unsigned_8 is (X);

   package With_Aspects is
      function "**" (X : Integer_8; Y: Integer_8) return Integer_8 with
        Import, Convention => Intrinsic;

      function "**" (X : Unsigned_8; Y: Natural) return Integer_8 with
        Import, Convention => Intrinsic;

      procedure Test_Pow;
   end;

   package body With_Aspects is
      procedure Test_Pow is
         X : Unsigned_8 := Id (200);
         Y : Integer_8 := X ** 2; --  This used to raise Constraint_Error
      begin
         null;
      end Test_Pow;
   end;

   package With_Pragmas is
      function "**" (X : Integer_8; Y: Integer_8) return Integer_8;
      pragma Import (intrinsic, "**");

      function "**" (X : Unsigned_8; Y: Natural) return Integer_8;
      pragma Import (intrinsic, "**");

      procedure Test_Pow;
   end;

   package body With_Pragmas is
      procedure Test_Pow is
         X : Unsigned_8 := Id (200);
         Y : Integer_8 := X ** 2; --  This used to raise Constraint_Error
      begin
         null;
      end Test_Pow;
   end;
begin
   With_Aspects.Test_Pow;
   With_Pragmas.Test_Pow;
end;
