procedure Cascade (X : in out Integer) is

   procedure Link_Output (Nid : Integer; Buf : Integer; Err : out Integer)
     with Global => null
   is
   begin
      Err := Nid + Buf;
   end Link_Output;

   T1, T2, T3, T4, T5 : Integer;
   Err : Integer;
begin
   T1 := X + X;
   if T1 > X then
      T2 := T1;
   else
      T2 := X;
   end if;
   T3 := T2 - T1;
   T4 := 2 * T3;
   T5 := (if T1 > T2 then T3 else T4);

   Link_Output (X, T5, Err);

   X := 10;
end Cascade;
