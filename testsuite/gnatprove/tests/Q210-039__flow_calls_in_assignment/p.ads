package P is
   function Fun return Integer with Annotate => (GNATprove, Always_Return);
end P;
