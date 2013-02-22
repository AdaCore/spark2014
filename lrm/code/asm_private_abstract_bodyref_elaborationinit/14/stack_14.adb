package body Stack_14
   with Refined_State => (State => Stack) -- refinement of state
is
   Stack : Stack_Type := Stack_Type'(Pointer => 0, S => Vector'(Index_Range => 0));
   -- initialization by elaboration of declaration

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
end Stack_14;
