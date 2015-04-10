package body Stacks_14.Monitored_14
  with SPARK_Mode
is
   subtype Index_Range is Stacks_14.Index_Range;

   overriding
   procedure Clear(S : out Monitored_Stack) is
   begin
      S.Stack_Pointer := 0;
      S.Stack_Vector := Stacks_14.Vector'(Index_Range => 0);
      S.Next_Identity_Value := 1;
      S.Monitor_Vector := Stacks_14.Vector'(Index_Range => 0);
   end Clear;

   overriding
   procedure Push(S : in out Monitored_Stack; X : in Integer) is
   begin
      Stacks_14.Push(Stacks_14.Stack (S), X);
      S.Monitor_Vector(S.Stack_Pointer) := S.Next_Identity_Value;
      S.Next_Identity_Value := S.Next_Identity_Value + 1;
   end Push;

   function Top_Identity(S : Monitored_Stack) return Integer is
     (if Is_Empty(S) then 0
      else S.Monitor_Vector(S.Stack_Pointer));

   function Next_Identity(S : Monitored_Stack) return Integer is
     (S.Next_Identity_Value);
end Stacks_14.Monitored_14;
