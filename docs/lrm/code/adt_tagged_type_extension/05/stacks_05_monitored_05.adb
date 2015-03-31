package body Stacks_05.Monitored_05 is
   subtype Index_Range is Stacks_05.Index_Range;

   overriding
   procedure Clear(S : out Monitored_Stack) is
   begin
      S.Stack_Pointer := 0;
      S.Stack_Vector := Stacks_05.Vector'(Index_Range => 0);
      S.Next_Identity_Value := 1;
      S.Monitor_Vector := Stacks_05.Vector'(Index_Range => 0);
   end Clear;

   overriding
   procedure Push(S : in out Monitored_Stack; X : in Integer) is
   begin
      Stacks_05.Push(Stacks_05.Stack(S), X);
      S.Monitor_Vector(S.Stack_Pointer) := S.Next_Identity_Value;
      S.Next_Identity_Value := S.Next_Identity_Value + 1;
   end Push;

   function Top_Identity(S : Monitored_Stack) return Integer is
      Result : Integer;
   begin
      if Is_Empty(S) then
         Result := 0;
      else
         Result := S.Monitor_Vector(S.Stack_Pointer);
      end if;
      return Result;
   end Top_Identity;

   function Next_Identity(S : Monitored_Stack) return Integer is
   begin
      return S.Next_Identity_Value;
   end Next_Identity;

end Stacks_05.Monitored_05;
