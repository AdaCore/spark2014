with Debug_Ops;

procedure Main is
   X : Integer := 0;
   Y : Integer := 0;
begin
   pragma Assert (X = Y); -- dummy check just to trigger .mlw generation
end;
