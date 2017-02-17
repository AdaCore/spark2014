package body Pack is

   procedure P0 (X : in out Boolean) is
   begin
      X := not X;
   end;

   procedure P1 is
   begin
      P0 (X);
   end;

   procedure P2 (X : in out Boolean) is
   begin
      P0 (X);
   end;

   procedure P3 is
      X : Boolean := True;
   begin
      P0 (X);
      -- pragma Assert (X);  --  incorrect assertion
   end;

   procedure P4 (X : in out Boolean) is
   begin
      X := not X;
   end;

   procedure P5 is
   begin
      P4 (X);
   end;

end;
