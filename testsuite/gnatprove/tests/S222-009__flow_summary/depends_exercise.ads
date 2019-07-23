package Depends_Exercise is

   Stack_Size : constant := 100;
   type Pointer_Range is range 0 .. Stack_Size;
   subtype Stack_Range is Pointer_Range range 1 .. Stack_Size;
   Stack : array (Stack_Range) of Integer;
   Stack_Pointer : Pointer_Range := 0;

   procedure Initialize
     with Global  => (Output => (Stack, Stack_Pointer)),
          Depends => ((Stack, Stack_Pointer) => null);

   procedure Push (X : in Integer)
     with Global  => (In_Out => (Stack, Stack_Pointer)),
          Depends => (Stack_Pointer => Stack_Pointer,
                      Stack         => (Stack, Stack_Pointer, X));

   function Is_Full return Boolean
     with Global  => (Input => Stack_Pointer),
          Depends => (Is_Full'Result => Stack_Pointer);

   function Wait_X_Return_True (X : in Integer) return Boolean
     with Depends => (Wait_X_Return_True'Result => null,
                      null => X);
end Depends_Exercise;
