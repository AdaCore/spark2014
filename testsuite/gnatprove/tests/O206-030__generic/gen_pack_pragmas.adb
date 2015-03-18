package body Gen_Pack_Pragmas is
   pragma Refined_State ((State => Constit));

   Constit : Integer := 0;

   function Func (Formal : Integer) return Integer is
      pragma Refined_Global
               ((Input =>
                  (Refs.External,
                   Outer,
                   Constit,
                   Pack_Inner)));

      pragma Refined_Depends
               ((Func'Result =>
                  (Refs.External,
                   Outer,
                   Constit,
                   Pack_Inner,
                   Formal)));
   begin
      return Formal;
   end Func;
end Gen_Pack_Pragmas;
