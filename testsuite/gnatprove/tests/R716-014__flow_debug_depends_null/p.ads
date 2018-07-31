package P with Abstract_State => (State with External) is
   procedure Read (Register :     Integer;
                   Value    : out Integer;
                   Verbose  :     Boolean)
   with
      Global  => (In_Out => State),
      Depends => ((Value, State) => (Register, State),
                  null => Verbose);
end;
