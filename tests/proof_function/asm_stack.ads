package ASM_Stack is

   function Is_Empty return Boolean;

   procedure Clear;
   pragma Postcondition (Is_Empty);

end ASM_Stack;
