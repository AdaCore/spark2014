package body Foo with
   Refined_State => (State_B => null), --  inconsitent refinement
   SPARK_Mode
is
end Foo;
