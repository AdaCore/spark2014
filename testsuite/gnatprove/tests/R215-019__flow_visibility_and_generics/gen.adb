package body Gen
  with Refined_State => (State => Constituent)
is
   Constituent : Integer := 0;

   function Foo_Ghost return Boolean
     with Refined_Global => Constituent
   is
   begin
      return Constituent = 0;
   end Foo_Ghost;

   procedure Proc
     with Refined_Global => (In_Out => Constituent)
   is
      A : Integer := Constituent;
   begin
      Constituent := A;
   end Proc;
end Gen;
