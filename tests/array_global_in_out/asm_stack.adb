package body ASM_Stack is
   procedure Push(X : in Integer)
   is
      type Vector is array(Integer range <>) of Integer;
      My_Vector : Vector (1 .. 10) := (others => 0);
      Stack_Top : Integer := 0;
   begin
      My_Vector(Stack_Top + 1) := X;
   end Push;
end ASM_Stack;
