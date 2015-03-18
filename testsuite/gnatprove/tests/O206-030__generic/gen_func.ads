with Refs;

generic
   Inner : Integer;

function Gen_Func (Formal : Integer) return Integer
  with Global =>
         (Input =>
           (Refs.External,
            Inner)),

       Depends =>
         (Gen_Func'Result =>
           (Refs.External,
            Inner,
            Formal)),

        Pre  => Formal >= -1,
        Post => Gen_Func'Result = Formal,
        Contract_Cases => (Formal < 0 => Gen_Func'Result < 0,
                           Formal = 0 => Gen_Func'Result = 0,
                           Formal > 0 => Gen_Func'Result > 0);
