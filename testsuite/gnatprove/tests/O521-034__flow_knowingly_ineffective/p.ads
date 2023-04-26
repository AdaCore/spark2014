package P is

  Dummy : Integer;

  procedure OK with No_Return,
     Exceptional_Cases => (others => False),
     Global => null;

  procedure OK_2 with No_Return,
     Exceptional_Cases => (others => False),
     Global => (Proof_In => Dummy);

end P;
