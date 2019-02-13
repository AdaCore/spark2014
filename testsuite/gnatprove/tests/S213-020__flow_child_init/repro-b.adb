package body Repro.B
with Refined_State => (BState => X)
is

   X : Byte := 0;

   -----------------------------------------------------------------------------

   function Get return Byte
   is (X);

   -----------------------------------------------------------------------------

   procedure Bar
   with Refined_Global => (In_Out => X)
   is
   begin
      X := X + 1;
   end Bar;

end Repro.B;
