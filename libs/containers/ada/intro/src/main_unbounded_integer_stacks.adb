with Unbounded_Integer_Stacks; use Unbounded_Integer_Stacks;
with Ada.Text_IO; use Ada.Text_IO;

procedure Main_Unbounded_Integer_Stacks is
   S : Stack := Create (4);
   X : Integer;

begin
   pragma Assert (Is_Empty (S));
   Push (S, 1);
   pragma Assert (not (Is_Empty (S)));
   Pop (S, X);
   Put_Line (Item => "First pop: " & Integer'Image (X));
   pragma Assert (X = 1);
   pragma Assert (Is_Empty (S));
   Push (S, 2);
   Push (S, 3);
   Push (S, 4);

   X := Pop (S);
   Put_Line (Item => "Second pop: " & Integer'Image (X));
   pragma Assert (X = 4);
   X := Pop (S);
   Put_Line (Item => "Third pop: " & Integer'Image (X));
   pragma Assert (X = 3);
   X := Pop (S);
   Put_Line (Item => "Fourth pop: " & Integer'Image (X));
   pragma Assert (X = 2);
   pragma Assert (Is_Empty (S));

   test_Pop_When_Empty (S);
   --  test pop when empty

   Put_Line ("This is the end, Main_Unbounded_Integer_Stacks");

end Main_Unbounded_Integer_Stacks;
