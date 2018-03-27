with Pkg;
procedure Main with Pre => Pkg.X = 0 is -- main subprogram
begin
   if Pkg.First_Call then
      Pkg.X := 123;
      Pkg.First_Call := False;
      Main; -- precondition not satisfied  -- @PRECONDITION:FAIL
   end if;
end Main;
