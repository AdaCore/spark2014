private package P2.Trace
  with SPARK_Mode => On
is
   procedure Put (S : String)
     with Global  => null,
          Depends => (null => S);
end P2.Trace;

