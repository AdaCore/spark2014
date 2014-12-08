pragma SPARK_Mode;
function Pi_Euler_2 return Long_Float is
   Index: Long_Integer;
   Pi, Erreur, Index_Float : Long_Float;
begin
   Pi := 0.0;
   Index := 0;
   Index_Float := 0.0;
   Erreur := 1.0;
   While not (Erreur<0.00000008) loop
      begin
         Index := Index+1;
         -- erreur := 1.0/Long_Float(Index)/Long_Float(Index);
         -- bug GNATProve sur les conversion Entier <=> Flottants
         Index_Float := Index_Float + 1.0;
         pragma Loop_Invariant (Index_Float in 1.0..Long_Float(Long_Integer'Last));
         Pragma Assert (Index_Float >= 1.0);
         Erreur := 1.0/Index_Float/Index_Float;
         Pi := Pi+Erreur;
      end;
   end loop;
   -- Pi := Sqrt(Pi*6.0);
   return (Pi);
end Pi_Euler_2;
