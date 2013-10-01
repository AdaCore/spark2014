package body Refined_Post_Legal
  with Refined_State => (State => X)
is
   X : Natural := 1;

   procedure Proc (Par  : in     Integer;
                   Par2 :    out Integer)
     with Refined_Global => X,
          Refined_Post   => Par2 = Par + X
   is
   begin
      Par2 := Par + X;
   end Proc;

   function Func (Par : Integer) return Integer
     with Refined_Global => X,
          Refined_Post   => Func'Result = Par + X
   is
   begin
      return Par + X;
   end Func;
end Refined_Post_Legal;
