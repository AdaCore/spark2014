procedure Bad_Align with SPARK_Mode is

   type U8 is mod 2 ** 8;
   type U64 is mod 2 ** 64;

   Var : aliased U8 := 0;

   function Alignment_Of_Var return U64 is (Var'Alignment) with Ghost;

   type R is record
      X : Integer;
   end record with Alignment => 4;

   Var2 : R;

   Data : Integer := Var2.X'Alignment;
begin
   null;
end Bad_Align;
