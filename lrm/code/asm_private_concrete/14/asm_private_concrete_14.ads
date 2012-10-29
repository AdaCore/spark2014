package asm_private_concrete_14
with
   Abstract_State => (S, Pointer)
is
   procedure Push(X : in Integer)
   with
      Global => In_Out => (S, Pointer);

   procedure Pop(X : out Integer)
   with
      Global => (Input  => S,
                 In_Out => Pointer);

private
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1..Stack_Size;
   type    Vector        is array(Index_Range) of Integer;

   S : Vector;
   Pointer : Pointer_Range;
end asm_private_concrete_14;
