with Ada.Text_IO;           use Ada.Text_IO;
with Ada.Integer_Text_IO;   use Ada.Integer_Text_IO;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Stacks;                use Stacks;

procedure Main is
   Max : Positive;
begin
   Put_Line ("how many elements in stack at most?");
   Get (Max);
   Skip_Line;

   declare
      Max_Cst : constant Positive := Max;
      S : Stack (Max_Cst);

   begin
      loop
         Put_Line ("push or pop element...");

         declare
            Cmd : String(1..20);
            Last : Integer;
            V   : Integer;
            Pos : Positive;
         begin
            Get_Line(Cmd, Last);
            if Last = 3 and then Cmd (1 .. 3) = "pop" then
               S.Pop;
               Put_Line ("stack is now: ");
               S.Print;
               New_Line;

            elsif Last >= 6 and then Cmd (1 .. 5) = "push " then
               Get (Cmd (6 .. Last), V, Pos);
               S.Push (Stacks.Element (V));
               Put_Line ("stack is now: ");
               S.Print;
               New_Line;

            elsif Cmd = "quit" then
               return;
            end if;
         end;
      end loop;
   end;
end Main;
