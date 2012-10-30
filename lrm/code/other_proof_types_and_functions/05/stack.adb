package body Stack
--# own State is My_Stack;
is
   My_Stack : Stack_Type;

   procedure Push(X : in Integer)
   --# global in out My_Stack;
   --# pre My_Stack.Pointer < Pointer_Range'Last;
   --# post My_Stack.Pointer /= 0;
   is
   begin
      My_Stack.Pointer := My_Stack.Pointer + 1;
      My_Stack.S(My_Stack.Pointer) := X;
   end Push;

end Stack;
