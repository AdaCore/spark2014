with Common; use Common;

procedure Integer_True_Check is
   MI : My_Integer := 0;
begin
   pragma Assert (Integer (MI) >= 0);
end;
