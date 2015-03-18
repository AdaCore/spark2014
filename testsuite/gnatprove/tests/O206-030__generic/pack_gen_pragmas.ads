with Refs;

package Pack_Gen_Pragmas is
   pragma Abstract_State (State);
   pragma Initializes ((State, Pack_Inner));

   generic
      Inner : Integer;

   function Func (Formal : Integer) return Integer;
   pragma Global
            ((Input =>
               (Refs.External,
                State,
                Pack_Inner,
                Inner)));

   pragma Depends
            ((Func'Result =>
               (Refs.External,
                State,
                Pack_Inner,
                Inner,
                Formal)));

   Pack_Inner : Integer := 0;
end Pack_Gen_Pragmas;
