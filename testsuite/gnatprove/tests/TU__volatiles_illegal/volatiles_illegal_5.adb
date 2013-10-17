package body Volatiles_Illegal_5
  with SPARK_Mode
is
   procedure Vol_Loop_Par (Par : in out Integer) is
   begin
      --  TU: 6. A constant, a discriminant or a loop parameter shall not be
      --  Volatile.
      for J in 0 .. Vol_Var loop
         Par := Par + 1;
      end loop;
   end Vol_Loop_Par;
end Volatiles_Illegal_5;
