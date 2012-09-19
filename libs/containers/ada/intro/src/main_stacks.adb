with Stacks; use Stacks;
with Ada.Text_IO; use Ada.Text_IO;

procedure Main_Stacks is
   S : Stack := Create (4);
   X : Integer;
begin
   pragma Assert (Is_Empty (S));
   Push (S, 1);
   pragma Assert (not (Is_Empty (S)));
   Pop (S, X);
   pragma Assert (X = 1);
   pragma Assert (Is_Empty (S));
   Put_Line (Item => "First pop: " & Integer'Image (X));
   Push (S, 2);
   Push (S, 3);
   Push (S, 4);
   X := Pop (S);
   pragma Assert (X = 4);
   Put_Line (Item => "Second pop: " & Integer'Image (X));
   X := Pop (S);
   pragma Assert (X = 3);
   Put_Line (Item => "Third pop: " & Integer'Image (X));
   X := Pop (S);
   pragma Assert (X = 2);
   pragma Assert (Is_Empty (S));
   Put_Line (Item => "Fourth pop: " & Integer'Image (X));
   Test_Pop_When_Empty (S);
   --  test pop

   for N in 1 .. Max_Size  loop
      Push (S, N);
   end loop;
   --  fulling the stack

   Test_Push_When_Full (S, 5);
   --  test push when stack is full

   for N in 1 .. Max_Size  loop
      X := Pop (S);
   end loop;
   --  clear out the stack

   Put_Line ("This is the end, Main_Stacks");

end Main_Stacks;
