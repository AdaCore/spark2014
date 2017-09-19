package Types is

   type Index is range 1 .. 8;

   subtype Sub_Index is Index range 3 .. 6;

   type Small_Index is range 1 .. 3;

   type Array_U is array (Index range <>) of Integer;

   type Array_C is array (Index range 1..5) of Integer;

   type Array_C2 is array (Index) of Integer;

   type NatByte is range 0..255;

   subtype IT1 is NatByte range  1..3;
   subtype IT2 is NatByte range  1..5;
   subtype IT3 is NatByte range  1..10;
   subtype ET1 is NatByte range  0..99;

   type AM is array (IT1 range <>, IT2 range <>, IT3 range <>) of ET1;

   function Dummy return AM;

end Types;
