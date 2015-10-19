package body Update_Checks_Multidim_Unconstr is

   -----------------------------------------
   --  multidimensional unconstrained arrays
   -----------------------------------------

   procedure Test1  (A       : in out AM;
                     X       : in IT1;
                     Y       : in IT2;
                     Z       : in IT3;
                     New_Val : in ET1)
   is
   begin
      A := A'Update ((X, Y, Z) => New_Val);  --  3 falsifiable checks
   end Test1;

   procedure Test3  (A       : in out AM;
                     X       : in IT1;
                     Y       : in IT2;
                     Z       : in IT3;
                     New_Val : in ET1)
   is
   begin
      if X > IT1'First and then Y > IT2'First and then Z < IT3'Last
        and then New_Val < ET1'Last then
         A := A'Update ((X - 1, Y - 1, Z + 1) => New_Val + 1);
      end if;
   end Test3;

   procedure Test4  (A       : in out AM;
                     X1, X2  : in IT1;
                     Y1, Y2  : in IT2;
                     Z1, Z2  : in IT3;
                     New_Val : in ET1)
   is
   begin
      --  6 falsifiable checks
      A := A'Update ((X1, Y1, Z1) | (X2, Y2, Z2) => New_Val);
   end Test4;

end Update_Checks_Multidim_Unconstr;
