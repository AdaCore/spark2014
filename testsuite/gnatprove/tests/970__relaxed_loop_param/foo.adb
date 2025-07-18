procedure Foo (S : out String)
  with Relaxed_Initialization => S
is
   Done : Boolean := False;
begin
   while not Done loop
      for J in 1 .. 3 loop
         S (J) := S (J);
      end loop;

      Done := True;
   end loop;
end;
