package body Repro.B
with Refined_State => (State => X)
is

   X : Byte := 0;

   -----------------------------------------------------------------------------

   function Get return Byte
   is (X);

end Repro.B;
