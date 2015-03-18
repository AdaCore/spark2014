with Refs;

package Pack_Gen
  with Abstract_State => State,
       Initializes    => (State, Pack_Inner)
is
   generic
      Inner : Integer;

   function Func (Formal : Integer) return Integer
     with Global =>
            (Input =>
              (Refs.External,
               State,
               Pack_Inner,
               Inner)),

          Depends =>
            (Func'Result =>
              (Refs.External,
               State,
               Pack_Inner,
               Inner,
               Formal));

   Pack_Inner : Integer := 0;
end Pack_Gen;
