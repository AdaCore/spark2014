with Ada.Text_IO;  use Ada.Text_IO;

package body Stacks is

   function Create (I : Positive := Default_Size) return Stack is
      Output : Stack (I);
   begin
      Output.Content := (others => Default_Value);

      --  Initial values

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

   function Peek (S : Stack) return Element is
   begin
      return S.Content (S.Index - 1);
   end Peek;

   function Pop (S : in out Stack) return Element is
      Output : Element;
   begin
      Pop (S, Output);
      return Output;
   end Pop;

   procedure Pop (S : in out Stack; X : out Element) is
   begin
      X := S.Content (S.Index - 1);
      S.Content (S.Index - 1) := Default_Value;

      --  Cleaning the occupied slot

      S.Index := S.Index - 1;
   end Pop;

   function Push (S : Stack; X : Element) return Stack is
      Output : Stack := S;
   begin

      --  Push (Output, X);
      --  Can not call Push procedure because it would leads to
      --  Infinite recursion. Instead we rewrite below the same procedure body

      Output.Content (S.Index) := X;
      Output.Index := S.Index + 1;
      return Output;
   end Push;

   procedure Push (S : in out Stack; X : Element) is
   begin
      S.Content (S.Index) := X;
      S.Index := S.Index + 1;
   end Push;

   --  Push a new element on the stack

end Stacks;
