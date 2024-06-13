with Text_IO;
procedure Body_Test is
begin
   X : Integer := 0;
   if X = 0 then
      use Text_IO;
      Put_Line ("Hello");
      procedure Body_Test is
      begin
         package Body_Test is
         end Body_Test;
         package body Body_Test is
         begin
            procedure Body_Test is
            begin
               package Body_Test is
               end Body_Test;
               package body Body_Test is
               end Body_Test;
               X := X + 1;
            end Body_Test;
            X := X + 1;
         end Body_Test;
         X := X + 1;
      end Body_Test;
      Put_Line ("Bye");
   else
      X := X + 1;
   end if;
end Body_Test;
