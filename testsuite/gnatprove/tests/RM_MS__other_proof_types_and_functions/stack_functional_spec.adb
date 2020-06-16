package body Stack_Functional_Spec
  with SPARK_Mode,
       Refined_State => (State => My_Stack)
is
   Initial_Stack : constant Stack_Type :=
     Stack_Type'(S       => Vector'(others => 0),
                 Pointer => 0);

   --  In this example the type used to represent the state
   --  abstraction and the actual type used in the implementation are
   --  the same, but they need not be. For instance S and Pointer
   --  could have been declared as distinct objects rather than
   --  composed into a record. Where the type representing the
   --  abstract state and the implementation of that state are
   --  different the function representing the abstract state has to
   --  convert implementation representation into the abstract
   --  representation. For instance, if S and Pointer were distinct
   --  objects the function State would have to return (S => S,
   --  Pointer => Pointer).
   My_Stack : Stack_Type;

   --  No conversion necessary as the abstract and implementation type
   --  is the same.
   function State return Stack_Type is (My_Stack)
     with Refined_Global => My_Stack;

   function Max_Stack_Size return Natural is (Stack_Size);

   function Count (S : Stack_Type) return Natural is (Natural (S.Pointer));

   function Stack_Entry (S : Stack_Type; N : Natural) return Integer is
     (S.S (Index_Range (N)));

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
end Stack_Functional_Spec;
