package Refined_State_Legal
  --  TU: 1. A Refined_State aspect of a ``package_body`` has visibility
  --  extended to the ``declarative_part`` of the body.
  with SPARK_Mode,
       Abstract_State => (S1, S2)
is
   procedure Do_Nothing;
end Refined_State_Legal;
