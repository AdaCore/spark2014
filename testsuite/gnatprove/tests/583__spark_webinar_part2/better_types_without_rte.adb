package body Better_Types_Without_RTE
  with SPARK_Mode
is

   procedure Assign
     (A    : in out Table;
      I, J : Index;
      P, Q : Element)
   is
   begin
      A (I + J)
                :=
                   P / Q;
   end Assign;

end Better_Types_Without_RTE;
