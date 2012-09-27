with Unbounded_Integer_Stacks;  use Unbounded_Integer_Stacks;
with Ada.Text_IO;               use Ada.Text_IO;

procedure Main_Unbounded_Integer_Stacks is
   S : Stack := Create;
   X : Integer;

   procedure Test_Pop_When_Empty (S : in out Stack);

   --  Test pop assertion
   --  This should be raised when the stack is empty

   procedure Test_Pop_When_Empty (S : in out Stack) is
      X : Integer;
   begin
      X := Pop (S);
      Put_Line ("Error: Pop on empty stack does not raise exception");
   exception
      when others =>
         Put_Line ("Ok: Pop on empty rstack raises exception");
   end Test_Pop_When_Empty;
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
   Put_Line (Item => "Stack.length before Fourth push"
             & Integer'Image (S.Cont_Ptr'Length));
   Push (S, 4);
   pragma Assert (4 = S.Cont_Ptr'Length);
   Put_Line (Item => "Stack.length after Fifth push"
             & Integer'Image (S.Cont_Ptr'Length));
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
   Test_Pop_When_Empty (S);

   --  Test pop when empty

   Put_Line ("This is the end, Main_Unbounded_Integer_Stacks");
end Main_Unbounded_Integer_Stacks;
