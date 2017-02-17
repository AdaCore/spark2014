package body Generic_Instance with SPARK_Mode is

   function Is_Valid (X : Root'Class) return Boolean is (X.F < Integer'Last);

   function F (X : Root'Class) return Boolean is (X.F > 0);

   procedure P (X : in out Root'Class) is
   begin
      X.F := 0;
   end P;

   procedure Test (X : in out Root'Class) is

      package My_Prop is new G_Prop (Root'Class, F, P);

   begin
      My_Prop.Q (X); --@PRECONDITION:FAIL
      pragma Assume (My_Prop.G (X)); --@PRECONDITION:FAIL
      pragma Assert (F (X)); --@PRECONDITION:FAIL
   end Test;


end Generic_Instance;
