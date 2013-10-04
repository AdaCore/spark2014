package Concat is

   type UC is array (Integer range <>) of Integer;

   subtype Index is Integer range 1 .. 10;
   subtype C is UC (Index);

   type CB is array (Index) of Integer;

   procedure P;
end Concat;
