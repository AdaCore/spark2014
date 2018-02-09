procedure Main with Global => null is

   type T is record
      C : Boolean;

      Dummy : String (1 .. 4096); -- just to force passing by reference
   end record;

   X : T := (C => True, Dummy => (others => ' '));

   procedure Bad (Y : in out T) with Pre => X.C is
   begin
      Y.C := False;
      pragma Assert (X.C);
   end;

begin
   Bad (X);
end;
