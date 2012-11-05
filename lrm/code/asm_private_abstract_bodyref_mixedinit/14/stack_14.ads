package Stack_14
   with Abstract_State => Stack,
        Initializes    => Stack
is
   procedure Push(X : in Integer)
      with Global => (In_Out => Stack);

   procedure Pop(X : out Integer)
      with Global => (In_Out => Stack);
private
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1..Stack_Size;
   type    Vector        is array(Index_Range) of Integer;
end Stack_14;
