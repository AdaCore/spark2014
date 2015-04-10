package body Stack_14
  with SPARK_Mode,
       Refined_State => (State => (S,
                                   Pointer)) -- State refinement
is
   Max_Stack_Size : constant := 1024;
   type Pointer_Range is range 0 .. Max_Stack_Size;
   subtype Index_Range is Pointer_Range range 1 .. Max_Stack_Size;
   type Vector is array (Index_Range) of Integer;

   -- Declaration of constituents
   S       : Vector;
   Pointer : Pointer_Range;

   -- The subprogram contracts are refined in terms of the constituents.
   -- Expression functions could be used where applicable

   function Is_Empty  return Boolean is (Pointer = 0)
     with Refined_Global => Pointer;

   function Is_Full  return Boolean is (Pointer = Max_Stack_Size)
     with Refined_Global => Pointer;

   function Top return Integer is (S (Pointer))
     with Refined_Global => (Pointer, S);

   procedure Push(X: in Integer)
     with Refined_Global => (In_Out => (Pointer, S))
   is
   begin
      Pointer := Pointer + 1;
      S (Pointer) := X;
   end Push;

   procedure Pop(X: out Integer)
     with Refined_Global => (Input  => S,
                             In_Out => Pointer)
   is
   begin
      X := S (Pointer);
      Pointer := Pointer - 1;
   end Pop;
begin
   -- Initialization - we promised to initialize the state
   -- and that initially the stack will be empty
   Pointer := 0;  -- Is_Empty is True.
   S := Vector'(Index_Range => 0);
end Stack_14;
