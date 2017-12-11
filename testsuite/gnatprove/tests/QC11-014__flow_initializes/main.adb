procedure Main (X : Boolean; Y : Boolean) with Pre => X, Global => null is

   package P with Initializes => null is
      pragma Assert (X);
      procedure Dummy with Global => null;
   end;

   package body P is
      procedure Dummy is null;
   begin
      declare
         Z : Boolean := Y;
         pragma Unreferenced (Z);
      begin
         null;
      end;
   end;

begin
   null;
end;
