package Unknown is
   function Value return Integer with Global => null, Annotate => (GNATprove, Always_Return);
end Unknown;
