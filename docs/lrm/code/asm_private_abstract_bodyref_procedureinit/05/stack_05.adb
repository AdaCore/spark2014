package body Stack_05
--# own State is Stack;
is
   Stack : Stack_Type;

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

   procedure Init
   --# global    out Stack;
   is
   begin
      Stack.Pointer := 0;
      Stack.S := Vector'(Index_Range => 0);
   end Init;
end Stack_05;
