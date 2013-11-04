package Q
  with SPARK_Mode,
       Initializes => Glob
is
   type IDX is range 1 .. 10;
   type IA is array (IDX) of Integer;

   Glob : Integer := 1;

   procedure Init1 (KS : out IA)
     with Depends => (KS => null);

   procedure Init2 (KS : out IA)
     with Depends => (KS => null);
end Q;
