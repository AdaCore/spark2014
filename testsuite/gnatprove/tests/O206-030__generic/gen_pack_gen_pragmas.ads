with Refs;

generic
   Outer : Integer;

package Gen_Pack_Gen_Pragmas is
   pragma Abstract_State (State);

   generic
      Inner : Integer;

   function Func (Formal : Integer) return Integer;
   pragma Global
            ((Input =>
               (Refs.External,
                Outer,
                State,
                Pack_Inner,
                Inner)));

   pragma Depends
            ((Func'Result =>
               (Refs.External,
                Outer,
                State,
                Pack_Inner,
                Inner,
                Formal)));

   Pack_Inner : Integer := 0;
end Gen_Pack_Gen_Pragmas;
