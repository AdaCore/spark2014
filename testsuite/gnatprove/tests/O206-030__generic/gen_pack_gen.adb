package body Gen_Pack_Gen
  with Refined_State => (State => Constit)
is
   Constit : Integer := 0;

   function Func (Formal : Integer) return Integer
     with Refined_Global =>
            (Input =>
              (Refs.External,
               Outer,
               Constit,
               Pack_Inner,
               Inner)),

          Refined_Depends =>
            (Func'Result =>
              (Refs.External,
               Outer,
               Constit,
               Pack_Inner,
               Inner,
               Formal))
   is
   begin
      return Formal;
   end Func;
end Gen_Pack_Gen;
