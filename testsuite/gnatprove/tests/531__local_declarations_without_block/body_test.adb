with Text_IO;
procedure Body_Test is
begin
   X : Integer := 0;
   if X = 0 then
      use Text_IO;
      Put_Line ("Hello");
      Put_Line ("Bye");
   else
      X := X + 1;
   end if;
end Body_Test;
