package Stack_14
  with SPARK_Mode,
       Abstract_State => (S_State, Pointer_State)
is
   procedure Push(X : in Integer)
     with Global => (In_Out => (S_State, Pointer_State));

   procedure Pop(X : out Integer)
     with Global => (Input  => S_State,
                     In_Out => Pointer_State);

private
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1..Stack_Size;
   type    Vector        is array(Index_Range) of Integer;

   S       : Vector with Part_Of => S_State;
   Pointer : Pointer_Range with Part_Of => Pointer_State;
end Stack_14;
