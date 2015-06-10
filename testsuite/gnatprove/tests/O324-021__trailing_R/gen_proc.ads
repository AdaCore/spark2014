with Refs;

generic

procedure Gen_Proc (Formal : out Integer)
  with Global =>
         (Input => Refs.External),

       Depends =>
         (Formal => Refs.External);
