package Protected_Sequence
  with SPARK_Mode
is
   protected P1 with Priority => 2 is
      procedure Set (Value : Integer);
   end P1;

   Data : Integer := 0 with Part_Of => P1;

   protected P2 with Priority => 3 is
      procedure Set (Value : Integer);
   end P2;

   task type TT with Priority => 1;

   T1, T2 : TT;

end Protected_Sequence;
