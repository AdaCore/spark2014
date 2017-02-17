package body Stack
  with SPARK_Mode,
       Refined_State => (State => My_Stack)
is
   Stack_Size : constant := 100;
   type    Pointer_Range is range 0 .. Stack_Size;
   subtype Index_Range   is Pointer_Range range 1 .. Stack_Size;
   type    Vector        is array(Index_Range) of Integer;

   type Stack_Type is record
      S : Vector;
      Pointer : Pointer_Range;
   end record;

   Initial_Stack : constant Stack_Type :=
     Stack_Type'(S       => Vector'(others => 0),
                 Pointer => 0);
   My_Stack : Stack_Type;

   function Max_Stack_Size return Natural is (Stack_Size);

   function Count return Natural is (Natural (My_Stack.Pointer))
     with Refined_Global => My_Stack;

   function Stack_Entry (N : Natural) return Integer is
     (My_Stack.S (Index_Range (N)))
     with Refined_Global => My_Stack;


   procedure Push(X : in Integer)
     with Refined_Global => (In_Out => My_Stack)
   is
   begin
      My_Stack.Pointer := My_Stack.Pointer + 1;
      My_Stack.S(My_Stack.Pointer) := X;
   end Push;

   procedure Pop (X : out Integer)
     with Refined_Global => (In_Out => My_Stack)
   is
   begin
      X := My_Stack.S (My_Stack.Pointer);
      My_Stack.Pointer := My_Stack.Pointer - 1;
   end Pop;

   procedure Swap2
     with Refined_Global => (In_Out => My_Stack)
   is
      Temp : Integer;
   begin
      Temp := My_Stack.S (My_Stack.Pointer);
      My_Stack.S (My_Stack.Pointer) := My_Stack.S (My_Stack.Pointer - 1);
      My_Stack.S (My_Stack.Pointer - 1) := Temp;
   end Swap2;
begin
   My_Stack := Initial_Stack;
end Stack;
