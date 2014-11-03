package body Volatiles_Illegal_5
  with SPARK_Mode
is
   procedure Vol_Loop_Par (Par : in out Integer) is
   begin
      --  TU: 6. A constant object (other than a formal parameter of
      --  mode **in**) shall not be effectively volatile. An
      --  effectively volatile object shall not have a discriminated
      --  part.
      for J in 0 .. Vol_Var loop
         Par := Par + 1;
      end loop;
   end Vol_Loop_Par;
end Volatiles_Illegal_5;
