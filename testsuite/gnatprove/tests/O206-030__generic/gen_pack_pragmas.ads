with Refs;

generic
   Outer : Integer;

package Gen_Pack_Pragmas is
   pragma Abstract_State (State);

   function Func (Formal : Integer) return Integer;
   pragma Global
            ((Input =>
               (Refs.External,
                Outer,
                State,
                Pack_Inner)));

   pragma Depends
            ((Func'Result =>
               (Refs.External,
                Outer,
                State,
                Pack_Inner,
                Formal)));

   Pack_Inner : Integer := 0;
end Gen_Pack_Pragmas;
