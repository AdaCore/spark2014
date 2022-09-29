package Core is
   Minus_One : constant Natural := -1;

   type Arr is array (Natural range 0 .. Minus_One) of Integer;

   type Rec is record
      Comp : Arr;
   end record;
end Core;
