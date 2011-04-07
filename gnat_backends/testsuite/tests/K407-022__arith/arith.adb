function Arith (X, Y, Z : Integer) return Integer is
   pragma Annotate (Formal_Proof, On);

   --  not ok
   Tmp1 : Integer := X + Y + Z;
   Tmp2 : Integer := X + Y - Z;
begin
   --  ok
   Tmp1 := (X + Y) + Z;
   Tmp2 := X + (Y - Z);

   --  not ok
   Tmp1 := X * Y mod Z;
   Tmp2 := X / Y * Z;

   --  ok
   Tmp1 := X * Y + Z;
   Tmp2 := X / Y - Z;

   --  not ok
   Tmp1 := X * (X - Y - Z) mod Z;

   --  not ok
   return Tmp2 - Tmp1 + X;
end;
