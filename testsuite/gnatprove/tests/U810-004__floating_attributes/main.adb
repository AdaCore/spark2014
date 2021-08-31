procedure Main (X : Float; Y : Integer) is

   --  Static and non-static uses of floating point attributes
   --  listed in Ada RM A.5.3 as "primitive function attributes".

   A1 : constant Integer := Float'Exponent (0.0);
   A2 : constant Integer := Float'Exponent (X);

   B1 : constant Float := Float'Compose (0.0, 1);
   B2 : constant Float := Float'Compose (X, Y);

   C1 : constant Float := Float'Fraction (0.0);
   C2 : constant Float := Float'Fraction (X);

   D1 : constant Float := Float'Scaling (0.0, 1);
   D2 : constant Float := Float'Scaling (X, Y);

   E1 : constant Float := Float'Unbiased_Rounding (0.0);
   E2 : constant Float := Float'Unbiased_Rounding (X);

   F1 : constant Float := Float'Machine_Rounding (0.0);
   F2 : constant Float := Float'Machine_Rounding (X);

   G1 : constant Float := Float'Adjacent (0.0, 1.0);
   G2 : constant Float := Float'Adjacent (X, X);

   H1 : constant Float := Float'Leading_Part (0.0, 1);
   H2 : constant Float := Float'Leading_Part (X, Y);

begin
   null;
end;
