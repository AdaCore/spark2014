with Unbounded_Stacks;
with Ada.Text_IO;  use Ada.Text_IO;

procedure Main_Unbounded_Stacks is

   package Integer_Stacks is new Unbounded_Stacks (Integer);
   use Integer_Stacks;
   S : Stack;
   X : Integer;
   package  Float_Stacks is new Unbounded_Stacks (Float);
   procedure test_Pop_When_Empty (S : in out Stack);
   procedure test_Pop_When_Empty (S : in out Stack) is
      X : Integer;
   begin
      X := Pop (S);
      Put_Line ("Error: Pop on empty stack does not raise exception");
   exception
      when others =>
         Put_Line ("Ok: Pop on empty stack raises exception");

         --  This should be raised when the stack is empty
   end test_Pop_When_Empty;

   --  Test pop assertion

begin

   --  Testing stack for Integer values

   S := Create;
   pragma Assert (Is_Empty (S));
   Push (S, 1);
   pragma Assert (not (Is_Empty (S)));
   Pop (S, X);
   Put_Line (Item => "First Integer pop: " & Integer'Image (X));
   pragma Assert (X = 1);
   pragma Assert (Is_Empty (S));
   Push (S, 2);
   Push (S, 3);
   pragma Assert (2 = S.Cont_Ptr'Length);
   Push (S, 4);
   pragma Assert (4 = S.Cont_Ptr'Length);
   X := Pop (S);
   Put_Line (Item => "Second Integer pop: " & Integer'Image (X));
   pragma Assert (X = 4);
   X := Pop (S);
   Put_Line (Item => "Third Integer pop: " & Integer'Image (X));
   pragma Assert (X = 3);
   X := Pop (S);
   Put_Line (Item => "Fourth Integer pop: " & Integer'Image (X));
   pragma Assert (X = 2);
   pragma Assert (Is_Empty (S));
   test_Pop_When_Empty (S);

--  Testing stack for Float values
   --
   declare
      T : Float_Stacks.Stack := Float_Stacks.Create;
      U : Float;
      use Float_Stacks;
      procedure test_Pop_When_Empty (S : in out Float_Stacks.Stack);
      procedure test_Pop_When_Empty (S : in out Float_Stacks.Stack) is
         X : Float;
      begin
         X := Pop (S);
         Put_Line ("Error: Pop on empty stack does not raise exception");
      exception
         when others =>
            Put_Line ("Ok: Pop on empty stack raises exception");

            --  This should be raised when the stack is empty

      end test_Pop_When_Empty;

   begin
      pragma Assert (Is_Empty (T));
      Push (T, 1.0);
      pragma Assert (not (Is_Empty (T)));
      Pop (T, U);
      Put_Line (Item => "First  Float pop  : " & Float'Image (U));
      pragma Assert (U = 1.0);
      pragma Assert (Is_Empty (T));
      Push (T, 2.0);
      Push (T, 3.0);
      pragma Assert (2 = T.Cont_Ptr'Length);
      Push (T, 4.0);
      pragma Assert (4 = T.Cont_Ptr'Length);
      U := Pop (T);
      Put_Line (Item => "Second  Float pop : " & Float'Image (U));
      pragma Assert (U = 4.0);
      U := Pop (T);
      Put_Line (Item => "Third  Float pop  : " & Float'Image (U));
      pragma Assert (U = 3.0);
      U := Pop (T);
      Put_Line (Item => "Fourth  Float pop : " & Float'Image (U));
      pragma Assert (U = 2.0);
      pragma Assert (Is_Empty (T));
      test_Pop_When_Empty (T);
   end;
   Put_Line ("This is the end, Main_Unbounded_Stacks");
end Main_Unbounded_Stacks;
