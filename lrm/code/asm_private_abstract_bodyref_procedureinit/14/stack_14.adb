package body Stack_14
   with Refined_State => (State => Stack)
is
   Stack : Stack_Type;

   procedure Push(X : in Integer)
      with Refined_Global => (In_Out => Stack)
   is
   begin
      Pointer := Pointer + 1;
      S(Pointer) := X;
   end Push;

   procedure Pop(X : out Integer)
      with Refined_Global => (In_Out => Stack)
   is
   begin
      X := S(Pointer);
      Pointer := Pointer - 1;
   end Pop;

   procedure Init
      with Refined_Global => (Output => Stack)
   is
   begin
      Stack.Pointer := 0;
      Stack.S := Vector'(Index_Range => 0);
   end Init;
end Stack_14;
