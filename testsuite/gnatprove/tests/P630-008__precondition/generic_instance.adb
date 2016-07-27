package body Generic_Instance with SPARK_Mode is

   function P (X : Root'Class) return Boolean is (X.F > 0);

   procedure Test (X : Root'Class) is

      package My_Prop is new G_Prop (Root'Class, P);

   begin
      pragma Assume (My_Prop.PP (X));
      pragma Assert (P (X));
   end Test;

end Generic_Instance;
