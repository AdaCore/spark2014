with My_String;

procedure Pkg (Put_Line : access procedure (Val : String);
	       X : in out Integer)
is
  S : constant My_String.My_String := "Hello World!";
begin
   X := X + 1;
   Put_Line (S);
end Pkg;
