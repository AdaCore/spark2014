package Lib is

   type Power_Of_Two is (One, Two, Four, Eight, Sixteen, Thirty_Two);
   for Power_Of_Two use (One        => 1,
                         Two        => 2,
                         Four       => 4,
                         Eight      => 8,
                         Sixteen    => 16,
                         Thirty_Two => 32);

   type Idx is new Power_Of_Two;

   subtype Int is Integer range 1 .. 42;

   type Rec is record
     F : Integer := 1;
   end record;

   type Arr is array (Idx) of Rec;

   Fourty_Two : constant Integer := 42;

   function Make_Array (X : Integer) return Arr;
   function Same (X : Integer := 42) return Integer;

end Lib;
