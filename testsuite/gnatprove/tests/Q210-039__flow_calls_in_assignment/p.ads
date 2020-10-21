package P is
   function Fun return Integer with Annotate => (GNATprove, Terminating);
end P;
