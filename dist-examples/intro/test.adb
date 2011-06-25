with Sat;         use Sat;
with Pricing;     use Pricing;
with Ada.Text_IO; use Ada.Text_IO;

procedure Test is
   I : constant Item   := (Price => 10, Number => 1);
   B : constant Basket := Basket'(1 => I);
   P : constant My_Int := Price_Of_Basket (B);
begin
   Put ("Price of basket is" & My_Int'Image (P));
end Test;
