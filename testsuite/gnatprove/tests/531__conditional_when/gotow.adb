with Ada.Text_IO; use Ada.Text_IO;
procedure Gotow is
  procedure Idk (Param : Boolean) is
  begin
     <<Here>>
     if Param then
        Put_Line ("Ok");
     end if;
     goto Here when Param;
  end;
begin
  null;
end;
