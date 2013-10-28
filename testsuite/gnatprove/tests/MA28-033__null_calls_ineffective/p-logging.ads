private package P.Logging
   with SPARK_Mode
is
   -- Sends A, B, C beyond the SPARK boundary.
   procedure Trace (A : in Integer;
		    B : in Boolean;
		    C : in Character)
     with Global => null,
          Depends => (null => (A, B, C));
   
end P.Logging;
