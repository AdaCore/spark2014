pragma SPARK_Mode;
with Interfaces; use Interfaces;
procedure Main is

   type U64 is mod 2 ** 64;
   type N_Array is array (Integer range <>) of Natural;
   Powers : constant N_Array := (63, 65);
begin
   pragma Assert (for all K of Powers => 2 ** K in U64'Range);
end Main;
