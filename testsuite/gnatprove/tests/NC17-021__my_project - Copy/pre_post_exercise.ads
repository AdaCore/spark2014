package Pre_Post_Exercise is

   Stack_Size : constant := 100;
   type Pointer_Range is range 0 .. Stack_Size;
   subtype Stack_Range is Pointer_Range range 1 .. Stack_Size;
   Stack : array (Stack_Range) of Integer;
   Stack_Pointer : Pointer_Range := 0;

   -- 1. Convert this to an expression function
   function Is_Full return Boolean
     with Global => (Input => Stack_Pointer);

   -- 2. Create an equivalent expression function to determine whether
   --    the stack is empty.

   -- 3. Add a suitable Post contract (making use of one of the
   --    expression functions.
   procedure Initialize
     with Global  => (Output => (Stack, Stack_Pointer));

   -- 4. Add a suitable Pre contract (making use of one of the expression
   --    functions). Prove that the code is free from run-time errors.
   procedure Push (X : in Integer)
     with Global  => (In_Out => (Stack, Stack_Pointer));

   -- 5. Add a suitable Pre contract (making use of one of the expression
   --    functions). Prove that the code is free from run-time errors.
   procedure Pop (X : out Integer)
     with Global  => (In_Out => Stack_Pointer,
                      Input  => Stack);

end Pre_Post_Exercise;
