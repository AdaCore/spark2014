package body Pack_Gen_Pragmas is
   pragma Refined_State ((State => Constit));

   Constit : Integer := 0;

   function Func (Formal : Integer) return Integer is
      pragma Refined_Global
               ((Input =>
                  (Refs.External,
                   Constit,
                   Pack_Inner,
                   Inner)));

      pragma Refined_Depends
               ((Func'Result =>
                  (Refs.External,
                   Constit,
                   Pack_Inner,
                   Inner,
                   Formal)));
   begin
      return Formal;
   end Func;
end Pack_Gen_Pragmas;
