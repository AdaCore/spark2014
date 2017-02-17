package body Stack_ASM
  with Refined_State => (State => (The_Stack, The_Ptr))
is



  type Length_T is range 0 .. 100;
  subtype Index_T is Length_T range 1 .. Length_T'Last;
  subtype Ptr_T   is Length_T;
  type Stack_T is array (Index_T) of Integer;

  The_Stack : Stack_T;
  The_Ptr   : Ptr_T;

  function Is_Empty return Boolean
    with Refined_Global => The_Ptr
  is
  begin
     return The_Ptr = 0;
  end Is_Empty;

  function Top return Integer
    with Refined_Global => (The_Stack, The_Ptr)
  is
  begin
     return The_Stack (The_Ptr);
  end Top;

  procedure Push (V : Integer)
    with Refined_Global => (In_Out => (The_Stack, The_Ptr))
  is
  begin
     The_Ptr := The_Ptr + 1;
     The_Stack (The_Ptr) := V;
  end Push;

  procedure Clear
    with Refined_Global => (Output => (The_Stack, The_Ptr))
  is
  begin
     The_Ptr := 0;
  end Clear;

  procedure Partial_Update
    with Refined_Global => (Output => The_Ptr)
  is
  begin
     The_Ptr := 0;
  end Partial_Update;

end Stack_ASM;
