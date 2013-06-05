package body Stack
   with Refined_State => (State => My_Stack)
is
   My_Stack : Stack_Type;

   function Is_Empty return Boolean
      with Refined_Global => (Input => My_Stack),
           Refined_Post   => Is_Empty'Result = (My_Stack.Pointer = 0)
   is
   begin
      return My_Stack.Pointer = 0;
   end Is_Empty;

   function Is_Full return Boolean
      with Refined_Global => (Input => My_Stack),
           Refined_Post   => Is_Full'Result = (My_Stack.Pointer = Pointer_Range'Last)
   is
   begin
      return My_Stack.Pointer = Pointer_Range'Last;
   end Is_Full;

   function Count return Natural
      with Refined_Global => (Input => My_Stack),
           Refined_Post   => Count'Result = My_Stack.Pointer
   is
   begin
      return My_Stack.Pointer;
   end Count;

   procedure Push(X : in Integer)
      with Refined_Global => (In_Out => My_Stack),
           Refined_Pre    => My_Stack.Pointer /= Pointer_Range'Last,
           Refined_Post   => My_Stack.Pointer /= 0
   is
   begin
      My_Stack.Pointer := My_Stack.Pointer + 1;
      My_Stack.S(My_Stack.Pointer) := X;
   end Push;

   procedure Swap2
      with Refined_Global => (In_Out => My_Stack),
           Refined_Pre    => My_Stack.Pointer >= 2,
           Refined_Post   => My_Stack.Pointer = My_Stack'Old.Pointer
   is
      Temp : Integer;
   begin
      Temp := My_Stack.S (1);
      My_Stack.S (1) := My_Stack.S (2);
      My_Stack.S (2) := Temp;
   end Swap2;

   procedure Initialize
      with Refined_Global => (Output => My_Stack),
           Refined_Post   => My_Stack.Pointer = 0
   is
   begin
      My_Stack := Initial_Stack;
   end Initialize;
end Stack;
