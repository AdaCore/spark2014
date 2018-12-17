with Ada.Text_IO;
with Interfaces;

procedure Init (S : out String) is

   pragma Warnings (Off, "initialization of ""*"" has no effect");
   package Unsigned8_IO is new Ada.Text_IO.Modular_IO (Interfaces.Unsigned_8);
   pragma Warnings (On, "initialization of ""*"" has no effect");
   --  Suppression doesn't seem to work for a predefined generic

   generic
   package P is
      X : Integer := 0;
   end;

   pragma Warnings (Off, "initialization of ""*"" has no effect");
   package My_P is new P;
   pragma Warnings (On,  "initialization of ""*"" has no effect");
   --  For user-written generic it doesn't work either

begin
   pragma Warnings (Off, "no Global contract available for ""Put""");
   Unsigned8_IO.Put
     (To   => S,
      Item => 0,
      Base => 16);
   pragma Warnings (On, "no Global contract available for ""Put""");
end;
