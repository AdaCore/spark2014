with Stacks;
with Ada.Text_IO;  use Ada.Text_IO;

procedure Main_Stacks is

   package Integer_Stacks is new Stacks (Integer, Default_Value => -1);
   use Integer_Stacks;

   S : Stack :=
     Create (Default_Size);
   X : Integer;

   procedure Test_Pop_When_Empty (S : in out Stack);

   --  Test pop assertion
   --  This should be raised when the stack is empty

   procedure Test_Push_When_Full (S : in out Stack; X : Integer);

   --  Test push assertion
   --  This should be raised when the stack is empty

   procedure Test_Pop_When_Empty (S : in out Stack) is
      X : Integer;
   begin
      X := Pop (S);
      Put_Line ("Error: Pop on empty stack does not raise exception");
   exception
      when others =>
         Put_Line ("Ok: Pop on empty stack raises exception");

   end Test_Pop_When_Empty;

   procedure Test_Push_When_Full (S : in out Stack; X : Integer) is
   begin

      Push (S, X);

   --  Test push when stack is full

      Put_Line ("Error: Push on Full stack does not raise exception");
   exception
      when others =>
         Put_Line ("Ok: Push on full stack raises exception");
   end Test_Push_When_Full;

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

   --  Test pop when stack is empty

   for N in 1 .. Default_Size  loop
      Push (S, N);
   end loop;

   --  Fulling the stack

   Test_Push_When_Full (S, 5);

   for N in 1 .. Default_Size  loop
      X := Pop (S);
   end loop;

   --  Clear out the stack

   Put_Line ("This is the end, Main_Stacks");

end Main_Stacks;
