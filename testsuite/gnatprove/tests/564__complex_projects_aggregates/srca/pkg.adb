with Interfaces.C;

procedure Pkg (X : in out Integer) is
   procedure Sub (X : in out Integer) is separate;
begin
   Sub (X);
   X := X + 1;
   Put_Line ("Hello World!");
end Pkg;
