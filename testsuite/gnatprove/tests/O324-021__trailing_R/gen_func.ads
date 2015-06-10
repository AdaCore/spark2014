with Refs;

generic

function Gen_Func (Formal : Integer) return Integer
  with Global =>
         (Input =>
           (Refs.External)),

       Depends =>
         (Gen_Func'Result =>
           (Refs.External,
            Formal));
