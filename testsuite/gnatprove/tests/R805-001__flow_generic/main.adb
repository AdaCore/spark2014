procedure Main (Arg : Float) with Global => null is

   generic
      X : Float;
   package G with Initializes => null is
      function Dummy return Integer is (0);
   end;

   package Outer with Initializes => null is
      package P is new G (Arg);
   end;
begin
   null;
end;
