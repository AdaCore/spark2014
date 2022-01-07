package P is

  Dummy : Integer;

  procedure OK with No_Return, Global => null;

  procedure OK_2 with No_Return, Global => (Proof_In => Dummy);

end P;
