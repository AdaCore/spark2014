procedure Main with SPARK_Mode is
   type My_Int is range 0 .. 9876543217
     with Default_Value => 36;
   type A is array (Positive range <>) of My_Int
     with Default_Component_Value => 42;
   X : A (1 .. 13) := (1 => <>, others => <>);
begin
   pragma Assert (X (1) = 36); --@ASSERT:FAIL
   pragma Assert (X (13) = 42);
end Main;
