--  Fake prover whose output and exit status are chosen by the FAKE_ANSWER
--  environment variable, so that a single binary can play the role of a
--  prover that concluded, one that ran out of memory, one that was killed
--  and printed nothing, and one that failed the way gappa does.

with Ada.Command_Line;
with Ada.Environment_Variables;
with Ada.Text_IO;

procedure Cvc5 is
   Answer : constant String :=
     Ada.Environment_Variables.Value ("FAKE_ANSWER", "");
begin
   if Answer = "unsat" then
      Ada.Text_IO.Put_Line ("unsat");
   elsif Answer = "alt_ergo" then
      Ada.Text_IO.Put_Line
        ("File ""vc.mlw"", line 1, characters 0-10: Valid (0.01) (3 steps)");
   elsif Answer = "steps" then
      Ada.Text_IO.Put_Line ("unknown (RESOURCEOUT)");
   elsif Answer = "memory" then
      Ada.Text_IO.Put_Line ("(error ""out of memory"")");
      Ada.Command_Line.Set_Exit_Status (101);
   elsif Answer = "gappa" then
      Ada.Text_IO.Put_Line ("some properties were not satisfied");
      Ada.Command_Line.Set_Exit_Status (1);
   end if;

   --  Any other value, in particular the empty one, means a prover that was
   --  killed before printing anything.
end Cvc5;
