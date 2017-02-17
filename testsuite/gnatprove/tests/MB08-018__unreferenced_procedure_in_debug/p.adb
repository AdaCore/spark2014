package body P
  with SPARK_Mode => On
is
   package Trace
   is
      --  This procedure should NOT be reported
      --  as unreferenced, since it appears in
      --  a pragma Debug below.
      procedure Print_Log (S : in String)
        with Global  => null,
             Depends => (null => S);

   end Trace;

   package body Trace is separate;

   procedure Inc_And_Log (X : in out Integer)
   is
   begin
      X := X + 1;
      pragma Debug (Trace.Print_Log ("Hello Rod"));
   end Inc_And_Log;
end P;
