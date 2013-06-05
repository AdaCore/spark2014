package body Stack_05
--# own State is Stack; -- refinement of state
is
   Stack : Stack_Type := Stack_Type'(Pointer => 0, S => Vector'(Index_Range => 0));
   -- initialization by elaboration of declaration

   procedure Push(X : in Integer)
   --# global in out Stack;
   is
   begin
      Stack.Pointer := Stack.Pointer + 1;
      Stack.S(Stack.Pointer) := X;
   end Push;

   procedure Pop(X : out Integer)
   --# global in out Stack;
   is
   begin
      X := Stack.S(Stack.Pointer);
      Stack.Pointer := Stack.Pointer - 1;
   end Pop;
end Stack_05;
