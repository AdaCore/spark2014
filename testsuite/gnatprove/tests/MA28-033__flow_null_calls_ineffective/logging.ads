package Logging
   with SPARK_Mode
is
   TestPoint : Integer := 0;

   -- Sends A beyond the SPARK boundary.
   procedure Trace1 (A : in Integer)
     with Global   => null,
          Depends  => (null => A),
          Always_Terminates;

   procedure Trace2
     with Global   => TestPoint,
          Depends  => (null => TestPoint),
          Always_Terminates;

   -- Sends A, B, C beyond the SPARK boundary.
   procedure Trace3 (A : in Integer;
                     B : in Boolean;
                     C : in Character)
     with Global   => null,
          Depends  => (null => (A, B, C)),
          Always_Terminates;

   -- Sends A to TestPoint and B to null
   procedure Trace_Mixed (A : in Integer;
                          B : in Boolean)
     with Global   => (Output => TestPoint),
          Depends  => (TestPoint => A,
                       null      => B),
          Always_Terminates;

end Logging;
