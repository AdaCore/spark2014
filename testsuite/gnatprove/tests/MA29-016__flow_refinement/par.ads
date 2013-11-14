package Par
   with Abstract_State => State
is

   X : Integer;

   procedure Stuff;

   --  par.pub|spec not visible here

private

   Y : Integer with Part_Of => State;

   function Wibble return Integer;

end Par;
