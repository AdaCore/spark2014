package body ASM_Stack

is
   Stack_Size : constant := 100;
   type Stack_Range is range 0 .. Stack_Size;
   type Vector is array(Stack_Range range <>) of Integer;
   Stack_Vector : Vector (1 .. Stack_Size) := (others => 1);
   Stack_Top  : Stack_Range := 0;

   function Is_Empty return Boolean
   is
       pragma Postcondition (Is_Empty'Result = (Stack_Top = 0));
   begin
      return Stack_Top = 0;
   end Is_Empty;

   procedure Clear
   is
   begin
      Stack_Top :=0;
      Stack_Vector := (others => 0);
   end Clear;

end ASM_Stack;
