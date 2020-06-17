pragma SPARK_Mode;
function Pi_Euler_2 return Long_Float is
   Index: Long_Integer range 1 .. Long_Integer'Last;
   Pi, Erreur : Long_Float;
   Index_Float : Long_Float range 1.0 .. Long_Float'Last;
begin
   Pi := 0.0;
   Index := 1;
   Index_Float := 1.0;
   Erreur := 1.0;
   While not (Erreur<0.00000008) loop
      begin
         -- erreur := 1.0/Long_Float(Index)/Long_Float(Index);
         -- bug GNATprove sur les conversion Entier <=> Flottants
         pragma Loop_Invariant (Index_Float >= 1.0);
         Pragma Assert (Index_Float >= 1.0);
         Erreur := 1.0/Index_Float/Index_Float;
         Pi := Pi+Erreur;
         Index := Index+1;
         Index_Float := Index_Float + 1.0;
      end;
   end loop;
   -- Pi := Sqrt(Pi*6.0);
   return (Pi);
end Pi_Euler_2;
