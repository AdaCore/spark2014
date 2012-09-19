with Ada.Text_IO; use Ada.Text_IO;
--  use GNAT;
package body Stacks is

   function Create (I : Positive := 1000)
                    return Stack  is
      output : Stack (I);
   begin
      Max_Size :=  I;
      output.Content := (others => Default_Value);
      --  initial values
      output.Index := 1;
      return output;
   end Create;

   function Is_Empty (S : Stack)
                      return Boolean is
   begin
      if S.Index = 1 then
         return True;
      else
         return False;
      end if;
   end Is_Empty;

   function Is_Full (S : Stack)
                     return Boolean is
   begin
      if S.Index = Max_Size + 1 then
         --  cause index points to the first free empty cell
         return True;
      else
         return False;
      end if;
   end Is_Full;

   procedure Push (S : in out Stack; X : Integer) is
   begin
         S.Content (S.Index) := X;
         S.Index := S.Index + 1;
   end Push;
   --  push a new element on the stack

   procedure Pop (S : in out Stack; X : out Integer)  is
   begin
         X := S.Content (S.Index - 1);
         S.Content (S.Index - 1) := Default_Value;
         --  cleaning the occupied slot
         S.Index := S.Index - 1;
   end Pop;

   function Pop (S : in out Stack)
                 return Integer is
      output : Integer := Default_Value;
   begin
      Pop (S, output);
      return output;
   end Pop;

   function Peek (S : Stack)
                  return Integer is
      output : Integer := Default_Value;
   begin
      output := S.Content (S.Index - 1);
      return output;
   end Peek;

   function Push (S : Stack; X : Integer)
                  return Stack is
      output : Stack := S;
   begin
      if not Is_Full (output) then
         output.Content (S.Index) := X;
         output.index := S.Index + 1;
         --  else
         --  should rise an exception
      end if;
      return output;
   end Push;

   procedure Test_Pop_When_Empty (S : in out Stack) is
      X : Integer;
   begin
      X := Pop (S);
      Put_Line ("Error: Pop on empty stack does not raise exception");
   exception
         --      When Assert_Failure =>
      when others =>
         Put_Line ("Ok: Pop on empty rstack raises exception");

   end Test_Pop_When_Empty;

   procedure Test_Push_When_Full (S : in out Stack; X : Integer) is
   begin
      Push (S, X);
      Put_Line ("Error: Push on Full stack does not raise exception");
   exception
         --      When Assert_Failure =>
      when others =>
         Put_Line ("Ok: Push on Full rstack raises exception");

   end Test_Push_When_Full;

end Stacks;
