with Refs;

generic
   Outer : Integer;

package Gen_Pack
  with Abstract_State => State
is
   function Func (Formal : Integer) return Integer
     with Global =>
            (Input =>
              (Refs.External,
               Outer,
               State,
               Pack_Inner)),

          Depends =>
            (Func'Result =>
              (Refs.External,
               Outer,
               State,
               Pack_Inner,
               Formal));

   Pack_Inner : Integer := 0;
end Gen_Pack;
