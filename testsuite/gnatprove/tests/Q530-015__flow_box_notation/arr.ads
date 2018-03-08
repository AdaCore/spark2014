package Arr is

   type My_Type is new Integer range 0 .. 10;

   type A is private;

   procedure Reset (This : out A);

private
   type A is array (My_Type) of My_Type;
end Arr;
