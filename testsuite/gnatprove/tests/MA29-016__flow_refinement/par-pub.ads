package Par.Pub
is

   A : Integer;

   function F return Integer is (Par.X); -- par|priv is not visible here

   procedure Stuff;

   -- par.priv|spec is not visible

private
   B : Integer;

   function G return Integer is (Par.X + Par.Y);
   -- par|spec is visible
   -- par|priv is visible

end Par.Pub;
