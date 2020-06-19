procedure Test_Delta_Discr_Checks with SPARK_Mode is

   type With_Discr (D : Boolean) is record
      case D is
      when True =>
         F1, F2 : Integer;
      when False =>
         G1, G2 : Integer;
      end case;
   end record;

   procedure Test_Discr_1 (X : in out With_Discr) with Pre => True is
   begin
      X := (X with delta G1 => 2); --@DISCRIMINANT_CHECK:FAIL
   end Test_Discr_1;

   procedure Test_Discr_2 (X : in out With_Discr) with Pre => True is
   begin
      X := X'Update (G1 => 2); --@DISCRIMINANT_CHECK:FAIL
   end Test_Discr_2;

   X : With_Discr := (D => True, others => 1);
begin
   Test_Discr_2 (X);
end Test_Delta_Discr_Checks;
