package body Test_Eq with SPARK_Mode is

   procedure P is
      R1 : constant R := (G => (1, 1));
      R2 : constant R := (G => (1, 2));
   begin
      pragma Assert (R1 = R2);
   end P;

end Test_Eq;
