package body Stack
--# own State is My_Stack;
is
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1..Stack_Size;
   type    Vector        is array(Index_Range) of Integer;

   type Stack_Type is record
      S : Vector;
      Pointer : Pointer_Range;
   end record;

   Initial_Stack : constant Stack_Type :=
      Stack_Type'(S       => Vector'(others => 0),
                  Pointer => 0);

   My_Stack : Stack_Type;

   procedure Push(X : in Integer)
   --# global in out My_Stack;
   --# pre My_Stack.Pointer < Stack_Size;
   is
   begin
      My_Stack.Pointer := My_Stack.Pointer + 1;
      My_Stack.S(My_Stack.Pointer) := X;
   end Push;

   procedure Pop (X : out Integer)
   --# global in out My_Stack;
   --# pre My_Stack.Pointer >= 1;
   is
   begin
      X := My_Stack.S (My_Stack.Pointer);
      My_Stack.Pointer := My_Stack.Pointer - 1;
   end Pop;

   procedure Swap2
   --# global in out My_Stack;
   --# post My_Stack.Pointer = My_Stack~.Pointer;
   is
      Temp : Integer;
   begin
      Temp := My_Stack.S (1);
      My_Stack.S (1) := My_Stack.S (2);
      My_Stack.S (2) := Temp;
   end Swap2;

   procedure Initialize
   --# global out My_Stack;
   --# post My_Stack.Pointer = 0;
   is
      --# for Initial_Stack declare Rule;
   begin
      My_Stack := Initial_Stack;
   end Initialize;
end Stack;
