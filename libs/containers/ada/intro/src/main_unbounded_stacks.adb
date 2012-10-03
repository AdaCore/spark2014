with Unbounded_Stacks;
with Ada.Text_IO;  use Ada.Text_IO;

procedure Main_Unbounded_Stacks is

   package Integer_Stacks is new Unbounded_Stacks (Integer);
   use Integer_Stacks;
   S : Stack;
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
   --
   S := Create;

   Put_Line ("This is the end, Main_Unbounded_Stacks");
end Main_Unbounded_Stacks;
