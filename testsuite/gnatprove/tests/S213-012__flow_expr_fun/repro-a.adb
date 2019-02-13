package body Repro.A
with Refined_State => (State => null)
is

   function Kind (Word : Word64) return Kind_Type
   is (Undefined);

   -----------------------------------------------------------------------------

   function Invariant return Boolean
   is (True);

end Repro.A;
