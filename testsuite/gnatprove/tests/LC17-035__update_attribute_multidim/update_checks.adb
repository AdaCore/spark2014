package body Update_Checks

is
   ----------------------------------------------------
   -- Tests for checks in program bodies with 'Update
   ----------------------------------------------------

   --  No checks generated, statically analysed by compiler.

   procedure Test1  (A       : in out A3;
                     X       : in IT1;
                     Y       : in IT2;
                     Z       : in IT3;
                     New_Val : in ET1)
   is
   begin
      A := A'Update ((X, Y, Z) => New_Val);
   end Test1;

   --  4 falsifiable checks:

   procedure Test2  (A       : in out A3;
                     X       : in IT1;
                     Y       : in IT2;
                     Z       : in IT3;
                     New_Val : in ET1)
   is
   begin
      A := A'Update ((X - 1, Y - 1, Z + 1) => New_Val + 1);
   end Test2;

   --  4 valid checks:

   procedure Test3  (A       : in out A3;
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

   --  No checks generated, statically analysed by compiler.

   procedure Test4  (A       : in out A3;
                     X1, X2  : in IT1;
                     Y1, Y2  : in IT2;
                     Z1, Z2  : in IT3;
                     New_Val : in ET1)
   is
   begin
      A := A'Update ((X1, Y1, Z1) | (X2, Y2, Z2) => New_Val);
   end Test4;

   --  7 falsifiable checks:

   procedure Test5  (A       : in out A3;
                     X1, X2  : in IT1;
                     Y1, Y2  : in IT2;
                     Z1, Z2  : in IT3;
                     New_Val : in ET1)
   is
   begin
      A := A'Update ((X1 - 1, Y1 - 1, Z1 - 1) |
                       (X2 + 1, Y2 + 1, Z2 + 1) => New_Val + 1);
   end Test5;

   --  7 valid checks:

   procedure Test6  (A       : in out A3;
                     X1, X2  : in IT1;
                     Y1, Y2  : in IT2;
                     Z1, Z2  : in IT3;
                     New_Val : in ET1)
   is
   begin
      if X1 > IT1'First and then Y1 > IT2'First and then Z1 > IT3'First
        and then X2 < IT1'Last and then Y2 < IT2'Last and then Z2 < IT3'Last
        and then New_Val < ET1'Last then
         A := A'Update ((X1 - 1, Y1 - 1, Z1 - 1) |
                          (X2 + 1, Y2 + 1, Z2 + 1) => New_Val + 1);
      end if;
   end Test6;

   --  11 falsifiable checks:

   procedure Test7  (A          : in out A3;
                     X1, X2, X3 : in IT1;
                     Y1, Y2, Y3 : in IT2;
                     Z1, Z2, Z3 : in IT3;
                     New_Val_1  : in ET1;
                     New_Val_2  : in ET1)
   is
   begin
      A := A'Update ((X1 - 1, Y1 - 1, Z1 - 1) |
                       (X2 + 1, Y2 + 1, Z2 + 1) => New_Val_1 + 1,
                     (X3 + 1, Y3 + 1, Z3 + 1)   => New_Val_2 - 1);
   end Test7;

   --  11 valid checks:

   procedure Test8  (A          : in out A3;
                     X1, X2, X3 : in IT1;
                     Y1, Y2, Y3 : in IT2;
                     Z1, Z2, Z3 : in IT3;
                     New_Val_1  : in ET1;
                     New_Val_2  : in ET1)
   is
   begin
      if X1 > IT1'First and then Y1 > IT2'First and then Z1 > IT3'First
        and then X2 < IT1'Last and then Y2 < IT2'Last and then Z2 < IT3'Last
        and then X3 < IT1'Last and then Y3 < IT2'Last and then Z3 < IT3'Last
        and then New_Val_1 < ET1'Last and then New_Val_2 > ET1'First then
         A := A'Update ((X1 - 1, Y1 - 1, Z1 - 1) |
                          (X2 + 1, Y2 + 1, Z2 + 1) => New_Val_1 + 1,
                        (X3 + 1, Y3 + 1, Z3 + 1)   => New_Val_2 - 1);
      end if;
   end Test8;

   --  11 valid checks:

   procedure Test9  (A          : in out A3;
                     X1, X2, X3 : in IT1;
                     Y1, Y2, Y3 : in IT2;
                     Z1, Z2, Z3 : in IT3;
                     New_Val_1  : in ET1;
                     New_Val_2  : in ET1)
   is
   begin
      A := A'Update ((X1 - 1, Y1 - 1, Z1 - 1) |
                       (X2 + 1, Y2 + 1, Z2 + 1) => New_Val_1 + 1,
                     (X3 + 1, Y3 + 1, Z3 + 1)   => New_Val_2 - 1);
   end Test9;

end Update_Checks;
