with Ada.Assertions;  use Ada.Assertions;
with Ada.Exceptions;  use Ada.Exceptions;

package body Indefinite_Stacks is

   function Create (Default : Item_Type) return Stack_Ptr  is
      output : Stack'(Item_Type);
   begin
      Stack.Next := Null;
      return output;
   end Create;

   function Is_Empty (S : Stack) return Boolean is
   begin
      if S.Next = Null then
         return True;
      else
         return False;
      end if;
   end Is_Empty;

   procedure Push (S : in out Stack_Ptr; X : Item_Type) is
      X_Ptr : Content_Ref := Item_Type'Access;
   begin
      S := new Stack'(S,X_Ptr);
   end Push;

   --  Push a new element on the stack

   procedure Pop (S : in out Stack_Ptr; X : out Item_Type)  is
   begin
      X := S.Object;

      --  cleaning the occupied slot
      --      S.Index := New_Index;
   end Pop;

   function Pop (S : in out Stack_Ptr) return Item_Type is
      output                       : Item_Type := Default_Value;
   begin
      Pop (S, output);
      return output;
   end Pop;

   function Peek (S : Stack_Ptr) return Item_Type is
      output                       : Item_Type := Default_Value;
   begin
      if not Is_Empty (S) then
         output := S.Object;
      end if;
      return output;
   end Peek;

   function Push (S : Stack_Ptr; X : Item_Type) return Stack is
      output : Stack_Ptr := S;
   begin
      Push (output, X);
      return output;
   end Push;

   procedure test_Pop_When_Empty (S : in out Stack) is
      X                            : Item_Type;
   begin
      X := Pop (S);
      Put_Line ("Error : Pop on empty stack does not raise exception");
   exception
      when others =>
         Put_Line ("Ok: Pop on empty rstack raises exception");
   end test_Pop_When_Empty;

end Indefinite_Stacks;
