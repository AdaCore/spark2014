package body Fast_Exponentiation with SPARK_Mode is

   function Fast_Exp (X : Int; N : Natural) return Int is
   begin
      if N = 0 then
         return 1;
      else
         declare
            R : constant Int := Fast_Exp (X, N / 2);
         begin
            if N rem 2 = 0 then
               return R * R;
            else
               return R * R * X;
            end if;
         end;
      end if;
   end Fast_Exp;

   function Fast_Exp_Imperative (X : Int; N : Natural) return Int is
      R : Int := 1;
      P : Int := X;
      E : Natural := N;
   begin
      while E > 0 loop
         pragma Loop_Invariant (R * P ** E = X ** N);
         pragma Loop_Variant (Decreases => E);

         declare
            P_At_L : constant Int := P with Ghost;
         begin
            if E rem 2 = 1 then
               R := R * P;
            end if;

            P := P * P;
            E := E / 2;

            pragma Assert (P ** E = (P_At_L) ** E * (P_At_L) ** E);
            pragma Assert (R * P ** E = X ** N);
         end;
      end loop;
      pragma Assert (E = 0);

      return R;
   end Fast_Exp_Imperative;

end Fast_Exponentiation;
