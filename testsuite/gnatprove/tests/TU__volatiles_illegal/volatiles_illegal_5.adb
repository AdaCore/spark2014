package body Volatiles_Illegal_5
  with SPARK_Mode
is
   procedure Vol_Loop_Par (Par : in out Integer) is
   begin
      --  TU: 4. A constant object (other than a formal parameter of
      --  mode **in**) shall not be effectively volatile.
      for J in 0 .. Vol_Var loop
         Par := Par + 1;
      end loop;
   end Vol_Loop_Par;
end Volatiles_Illegal_5;
