procedure Bug_Align with SPARK_Mode is

   type U8 is mod 2 ** 8;
   type U64 is mod 2 ** 64;

   Var : aliased U8 := 0 with Alignment => 16;

   function Alignment_Of_Var return U64 is (Var'Alignment) with Ghost;

begin
    pragma Assert (Alignment_Of_Var = 1); --@ASSERT:FAIL
end Bug_Align;
