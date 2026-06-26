with Interfaces; use Interfaces;
with G;
procedure Test with SPARK_Mode is

   --  Test that we emit an explanation when we cannot deduce the size of a
   --  component in UC checks because it is an array with dynamic bounds.

   type R is record
      F, G : Integer_8;
   end record;

   package I is new G (R);
begin
   null;
end Test;
