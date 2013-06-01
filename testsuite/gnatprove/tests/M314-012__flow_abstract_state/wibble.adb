package body Stack_ASM
  with Refined_State => (State => (The_Stack, The_Ptr))
is

  type Length_T is range 0 .. 100;
  subtype Index_T is Length_T range 1 .. Length_T'Last;
  subtype Ptr_T   is Length_T;
  type Stack_T is array (Index_T) of Integer;

  The_Stack : Stack_T;
  The_Ptr   : Ptr_T;

  function Is_Empty return Boolean is
  begin
     return The_Ptr = 0;
  end Is_Empty;

  function Top return Integer is
  begin
     return The_Stack (The_Ptr);
  end Top;

  procedure Push (V : Integer) is
  begin
     The_Ptr := The_Ptr + 1;
     The_Stack (The_Ptr) := V;
  end Push;

  procedure Clear is
  begin
     The_Ptr := 0;
  end Clear;

end Stack_ASM;
