with Ada.Text_IO;         use Ada.Text_IO;
with Ada.Integer_Text_IO; use Ada.Integer_Text_IO;
with Stacks;              use Stacks;

procedure Main is pragma SPARK_Mode (Off); --  tagged types
   Max : Positive;
begin
   Put_Line ("how many elements in stack at most?");
   Get (Max);
   Skip_Line;

   declare
      S : Stack (Max);

   begin
      loop
         Put_Line ("push or pop element...");

         declare
            Cmd : constant String := Get_Line;
            V   : Integer;
            Pos : Positive;

         begin
            if Cmd'Length = 3 and then Cmd (1 .. 3) = "pop" then
               S.Pop;
               Put_Line ("stack is now: ");
               S.Print;
               New_Line;

            elsif Cmd'Length >= 6 and then Cmd (1 .. 5) = "push " then
               Get (Cmd (6 .. Cmd'Last), V, Pos);
               S.Push (Element (V));
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
