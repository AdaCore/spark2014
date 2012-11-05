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
   end;

   function Is_Full return Boolean
      with Refined_Global => (Input => My_Stack),
           Refined_Post   => Is_Full'Result = (My_Stack.Pointer = Pointer_Range'Last)
   is
   begin
      return My_Stack.Pointer = Pointer_Range'Last;
   end;

   procedure Push(X : in Integer)
      with Refined_Global => (In_Out => My_Stack),
           Refined_Pre    => My_Stack.Pointer /= Pointer_Range'Last,
           Refined_Post   => My_Stack.Pointer /= 0
   is
   begin
      My_Stack.Pointer := My_Stack.Pointer + 1;
      My_Stack.S(My_Stack.Pointer) := X;
   end Push;

   procedure Initialize
      with Refined_Global => (Output => My_Stack),
           Refined_Post   => My_Stack.Pointer = 0
   is
      --  Note that a rule declaration annotation is included at this
      --  point in the SPARK 2005 code. The corresponding SPARK 2014
      --  syntax is TBD.
   begin
      My_Stack := Initial_Stack;
   end Initialize;
end Stack;
