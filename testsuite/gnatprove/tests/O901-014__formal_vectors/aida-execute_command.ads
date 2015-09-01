with Aida.Strings;

-- The origin of this code is a code snippet posted by Gautier de Montmollin on the usenet group comp.lang.ada.
-- For example, to execute gprbuild to build the Aida library from within an Ada application write:
--
--     declare
--        Exit_Status : Integer;
--     begin
--        Aida.Command_Line.Execute_Command ("gprbuild -P aida.gpr", Exit_Status, );
--        if Exit_Status = 0 then
--           Ada.Text_IO.Put_Line ("Process terminated normally");
--        else
--           Ada.Text_IO.Put_Line ("Process terminated abnormally");
--        end if;
--     end;
procedure Aida.Execute_Command (Command     : in String;
                                Exit_Status : out Integer;
                                Output      : out Aida.Strings.Unbounded_String_Type);
