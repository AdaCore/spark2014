package Logging
   with SPARK_Mode
is
   TestPoint : Integer := 0;

   -- Sends A beyond the SPARK boundary.
   procedure Trace1 (A : in Integer)
     with Global   => null,
          Depends  => (null => A),
          Annotate => (GNATprove, Always_Return);

   procedure Trace2
     with Global   => TestPoint,
          Depends  => (null => TestPoint),
          Annotate => (GNATprove, Always_Return);

   -- Sends A, B, C beyond the SPARK boundary.
   procedure Trace3 (A : in Integer;
                     B : in Boolean;
                     C : in Character)
     with Global   => null,
          Depends  => (null => (A, B, C)),
          Annotate => (GNATprove, Always_Return);

   -- Sends A to TestPoint and B to null
   procedure Trace_Mixed (A : in Integer;
                          B : in Boolean)
     with Global   => (Output => TestPoint),
          Depends  => (TestPoint => A,
                       null      => B),
          Annotate => (GNATprove, Always_Return);

end Logging;
