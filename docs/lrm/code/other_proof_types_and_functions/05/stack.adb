package body Stack
--# own State is My_Stack;
is
   My_Stack : Stack_Type;

   procedure Push(X : in Integer)
   --# global in out My_Stack;
   --# post My_Stack.Pointer /= 0;
   is
   begin
      My_Stack.Pointer := My_Stack.Pointer + 1;
      My_Stack.S(My_Stack.Pointer) := X;
   end Push;

   procedure Swap2
   --# global in out My_Stack;
   --# post My_Stack.Pointer = My_Stack~.Pointer;
   is
      Temp : Integer;
   begin
      Temp := My_Stack.S (1);
      My_Stack.S (1) := My_Stack.S (2);
      My_Stack.S (2) := Temp;
   end Swap2;

   procedure Initialize
   --# global out My_Stack;
   --# post My_Stack.Pointer = 0;
   is
      --# for Initial_Stack declare Rule;
   begin
      My_Stack := Initial_Stack;
   end Initialize;

end Stack;
