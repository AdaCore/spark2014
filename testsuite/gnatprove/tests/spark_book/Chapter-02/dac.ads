package DAC is
-- Package stub for Chapter 2 code snippets

   procedure Write (Value : in Integer)
     with
       Global => null,
       Annotate => (GNATprove, Always_Return);

end DAC;
