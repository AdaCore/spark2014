procedure Main2 (Arg : Float) with Global => null is

   generic
      X : Float;
   package G is
   end;

   package Outer is
      package P is new G (Arg);
   end;
begin
   null;
end;
