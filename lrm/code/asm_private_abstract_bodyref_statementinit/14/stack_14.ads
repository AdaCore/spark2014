package Stack_14
   with Abstract_State => State,
        Initializes    => State
is
   procedure Push(X : in Integer)
      with Global => (In_Out => State);

   procedure Pop(X : out Integer)
      with Global => (In_Out => State);
private
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1..Stack_Size;
   type    Vector        is array(Index_Range) of Integer;

   type Stack_Type is
      record
         S : Vector;
         Pointer : Pointer_Range;
      end record;
end Stack_14;
