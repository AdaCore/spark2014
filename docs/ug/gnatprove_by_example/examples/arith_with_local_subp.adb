package body Arith_With_Local_Subp
  with SPARK_Mode
is
   --  Local procedure without external visibility
   procedure Increment_In_Body (X : in out Integer) is
   begin
      X := X + 1;
   end Increment_In_Body;

   procedure Add_Two (X : in out Integer) is

      --  Local procedure defined inside Add_Two
      procedure Increment_Nested (X : in out Integer) is
      begin
         X := X + 1;
      end Increment_Nested;

   begin
      Increment_In_Body (X);
      Increment_Nested (X);
   end Add_Two;

end Arith_With_Local_Subp;
