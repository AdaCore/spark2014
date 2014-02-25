package Update_Checks
is
   type NatByte is range 0..255;

   subtype IT1 is NatByte range  1..3;
   subtype IT2 is NatByte range  1..5;
   subtype IT3 is NatByte range  1..10;
   subtype ET1 is NatByte range  0..99;

   type A3 is array (IT1, IT2, IT3) of ET1;

   --  Mixed 'Update choices, 11 valid checks, valid postcondition:

   procedure Test9  (A          : in out A3;
                     X1, X2, X3 : in IT1;
                     Y1, Y2, Y3 : in IT2;
                     Z1, Z2, Z3 : in IT3;
                     New_Val_1  : in ET1;
                     New_Val_2  : in ET1)
     with
     Pre =>  X1 > IT1'First and then Y1 > IT2'First and then Z1 > IT3'First
       and then X2 < IT1'Last and then Y2 < IT2'Last and then Z2 < IT3'Last
       and then X3 < IT1'Last and then Y3 < IT2'Last and then Z3 < IT3'Last
       and then New_Val_1 < ET1'Last and then New_Val_2 > ET1'First,
     Post =>
     A = A'Old'Update ((X1 - 1, Y1 - 1, Z1 - 1) |
                         (X2 + 1, Y2 + 1, Z2 + 1) => New_Val_1 + 1,
                       (X3 + 1, Y3 + 1, Z3 + 1)   => New_Val_2 - 1);

   -- See body for tests of checks of 'Update in subprogram bodies

end Update_Checks;
