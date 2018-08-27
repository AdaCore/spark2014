procedure Main1 (Arg : Float) with Global => null is

   generic
      X : Float;
   package G with Initializes => null is
   end;

   package Outer with Initializes => null is
      package P is new G (Arg);
   end;
begin
   null;
end;
