package body LT
  with SPARK_Mode => On
is
   function Total (X : in Table) return Sum is
      R : Sum;
   begin
      R := 0;
      for I in N loop

	 for J in N loop
	    R := R + X (I)(J);
	    pragma Loop_Invariant (R <= ((I * 10) + J + 1));
	 end loop;

         pragma Loop_Invariant (R <= (I + 1) * 10);
      end loop;
      return R;
   end Total;

end LT;
