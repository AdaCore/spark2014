with Ada.Unchecked_Conversion;

package P is

  type U4 is mod 2 ** 4;

   type My_Rec is record
      F0 : U4;
      F1 : U4;
      F2 : U4;
      F3 : U4;
      F4 : U4;
      F5 : U4;
      F6 : U4;
      F7 : U4;
   end record
   with Size => 32, Object_Size => 32;

   for My_Rec use
     record
       F0 at 0 range 0 .. 3;
       F1 at 0 range 4 .. 7;
       F2 at 0 range 8 .. 11;
       F3 at 0 range 12 .. 15;
       F4 at 0 range 16 .. 19;
       F5 at 0 range 20 .. 23;
       F6 at 0 range 24 .. 27;
       F7 at 0 range 28 .. 31;
     end record;

   type My_Arr is array (0 .. 1) of My_Rec
   with Size => 64, Object_Size => 64;

   type I is mod 2 ** 64;

   function My_UC is new
     Ada.Unchecked_Conversion
       (Source => I,
        Target => My_Arr);

end P;
