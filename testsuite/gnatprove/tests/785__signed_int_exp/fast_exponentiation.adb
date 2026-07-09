package body Fast_Exponentiation
  with SPARK_Mode
is

   function Fast_Exp (X : Base_Range; N : Exp_Range) return Natural is
      R : Natural := 1;
      P : Natural := X;
      E : Natural := N;
   begin
      while E > 0 loop
         pragma Loop_Invariant (R * P ** E = X ** N);
         pragma Loop_Variant (Decreases => E);

         if E rem 2 = 1 then
            R := R * P;
         end if;

         P := P * P;
         E := E / 2;

         pragma Assert (R * P ** E = X ** N);
      end loop;

      return R;
   end Fast_Exp;

   function Fast_Exp_Recursive (X : Base_Range; N : Exp_Range) return Natural
   is
   begin
      if N = 0 then
         return 1;
      else
         declare
            R : constant Natural := Fast_Exp_Recursive (X, N / 2);
         begin
            if N rem 2 = 0 then
               return R * R;
            else
               return R * R * X;
            end if;
         end;
      end if;
   end Fast_Exp_Recursive;

end Fast_Exponentiation;
