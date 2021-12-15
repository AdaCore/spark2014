with Ada.Text_IO;
with GNAT.Expect;
with GNAT.OS_Lib;

procedure Aida.Execute_Command (Command     : in String;
                                Exit_Status : out Integer;
                                Output      : out Aida.Strings.Unbounded_String_Type)
is
   Fd      : GNAT.Expect.Process_Descriptor;
   Result  : GNAT.Expect.Expect_Match;
   Timeout : Integer := 100_000;

   Arguments : GNAT.OS_Lib.Argument_List_Access;
begin
   --   Ada.Text_IO.Put_Line(Command);
   Output.Initialize ("");
   Arguments := GNAT.OS_Lib.Argument_String_To_List (Command);
   GNAT.Expect.Non_Blocking_Spawn
     (Fd,
      Command    => Arguments (Arguments'First).all,
      Args       => Arguments (Arguments'First + 1 .. Arguments'Last),
      Err_To_Out => True);

   loop
      begin
         GNAT.Expect.Expect (Fd, Result, "\n", Timeout);
         case Result is
            when GNAT.Expect.Expect_Timeout =>
               Ada.Text_IO.Put ("[timeout]"); -- no output for this time slice
            when GNAT.Expect.Expect_Full_Buffer =>
               Ada.Text_IO.Put ("[full]"); -- doesn't happen with buffer size = 0 ?
            when 1 =>
               Output.Append (GNAT.Expect.Expect_Out (Fd)); -- regexp matched
            when others =>
               Ada.Text_IO.Put ("[?]"); -- shouldn't (and doesn't) happen
         end case;
      exception
         when GNAT.Expect.Process_Died =>
            exit;
      end;
   end loop;

   GNAT.Expect.Close (Fd, Exit_Status);
end Aida.Execute_Command;
