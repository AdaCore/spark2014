pragma SPARK_Mode;
function Pi_Euler return Long_Float is
   Index: Positive;
   Pi, Erreur : Long_Float;
begin
   Pi := 0.0;
   Index := 1;
   Erreur := 1.0;
   While not (Erreur<0.00000008) loop
      begin
         pragma Loop_Invariant (Index >= 1);
         pragma Assert (Long_Float(Index) >= 1.0);
         Erreur := 1.0/Long_Float(Index);  --  @OVERFLOW_CHECK:PASS
         Pi := Pi+Erreur;
         Index := Index+1;
      end;
   end loop;
   -- Pi := Sqrt(Pi*6.0);
   return (Pi);
end Pi_Euler;
