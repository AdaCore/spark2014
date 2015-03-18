with Refs;

generic
   Outer : Integer;

package Gen_Pack_Gen
  with Abstract_State => State
is
   generic
      Inner : Integer;

   function Func (Formal : Integer) return Integer
     with Global =>
            (Input =>
              (Refs.External,
               Outer,
               State,
               Pack_Inner,
               Inner)),

          Depends =>
            (Func'Result =>
              (Refs.External,
               Outer,
               State,
               Pack_Inner,
               Inner,
               Formal));

   Pack_Inner : Integer := 0;
end Gen_Pack_Gen;
