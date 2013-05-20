package body Test
is
   type T1 is array (1..10) of Integer;
   type T2 is array (1..10, 1..10) of Integer;

   function F return T1 is
   begin
      return (1..10 => 1);
   end F;

   function F return T2 is
   begin
      return (1..10 => (1..10 => 2));
   end F;

   function Test_01 return Integer is
   begin
      return F (7);
   end Test_01;

end Test;
