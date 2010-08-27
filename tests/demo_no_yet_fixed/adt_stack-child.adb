--  mutual recursion

package body ADT_Stack.Child
is
   procedure Clear(S : out Child_Stack)
   is
      subtype Index_Range is ADT_Stack.Stack_Range;
   begin
      ADT_Stack.Clear(ADT_Stack.Stack(S));
      S.Next_Value := 1;
      S.Child_Stack_Vector := (others => 0);
   end Clear;

   procedure Push(S : in out Child_Stack; X : in Integer)
   is
   begin
      ADT_Stack.Push(ADT_Stack.Stack(S), X);
      S.Child_Stack_Vector (S.Stack_Top) := Integer(S.Next_Value);
      S.Next_Value := S.Next_Value + 1;
   end Push;

   function Top_Identity(S : Child_Stack) return Integer
   is
      Result : Integer;
   begin
      if Is_Empty(S) then
         Result := 0;
      else
         Result := Integer (s.Child_Stack_Vector (S.Stack_Top));
      end if;
      return Result;
   end Top_Identity;


end ADT_Stack.Child;
