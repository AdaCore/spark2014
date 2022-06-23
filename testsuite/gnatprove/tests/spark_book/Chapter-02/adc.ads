package ADC is
-- Package stub for Chapter 2 code snippets

   procedure Read (Value : out Integer)
     with
       Global => null,
       Annotate => (GNATprove, Always_Return);

end ADC;
