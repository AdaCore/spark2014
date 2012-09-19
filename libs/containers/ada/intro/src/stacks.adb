with Ada.Text_IO; use Ada.Text_IO;
--  use GNAT;
package body Stacks is

   function Create (I : Positive := Default_Size) return Stack is
      Output : Stack (I);
   begin
      Output.Content := (others => Default_Value);
      --  initial values
      Output.Index := 1;
      return Output;
   end Create;

   function Is_Empty (S : Stack) return Boolean is
   begin
      return S.Index = 1;
   end Is_Empty;

   function Is_Full (S : Stack) return Boolean is
   begin
      return S.Index > S.Size;
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

   function Pop (S : in out Stack) return Integer is
      Output : Integer;
   begin
      Pop (S, Output);
      return Output;
   end Pop;

   function Peek (S : Stack) return Integer is
   begin
      return S.Content (S.Index - 1);
   end Peek;

   function Push (S : Stack; X : Integer) return Stack is
      Output : Stack := S;
   begin
      Push (Output, X);
      return Output;
   end Push;
end Stacks;
