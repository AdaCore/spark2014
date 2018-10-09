procedure Main3 (Arg : Float) with Global => null is

   generic
      X1 : Float;
   package G1 is
   end;

   generic
      X2 : Float;
   package G2 is
      package I1 is new G1 (X2);
   end;

   package Outer is
      package I2 is new G2 (Arg);
   end;
begin
   null;
end;
