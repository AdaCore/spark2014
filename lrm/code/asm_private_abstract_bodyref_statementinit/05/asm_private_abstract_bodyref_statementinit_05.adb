package body asm_private_abstract_bodyref_statementinit_05
--# own State is Stack;  -- refinement of state
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
begin  -- initialized by package body statements
   Stack.Pointer := 0;
   Stack.S := Vector'(Index_Range => 0);
end asm_private_abstract_bodyref_statementinit_05;
