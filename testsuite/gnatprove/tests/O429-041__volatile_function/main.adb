with Vol_Fun;
procedure Main is
   X : Integer := Vol_Fun.F (1);
   Y : Integer := Vol_Fun.F (1);
begin
   pragma Assert (X = Y); -- @ASSERT:FAIL
end Main;
