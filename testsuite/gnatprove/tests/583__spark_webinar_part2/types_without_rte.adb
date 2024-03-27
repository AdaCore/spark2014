package body Types_Without_RTE
  with SPARK_Mode
is

   procedure Assign
     (A    : in out Table;
      I, J : Index;
      P, Q : Integer)
   is
   begin
      A (I + J)
                :=
                   P / Q;
   end Assign;

end Types_Without_RTE;
