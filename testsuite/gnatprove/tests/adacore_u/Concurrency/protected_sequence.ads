package Protected_Sequence
  with SPARK_Mode
is
   protected P1 is
      pragma Priority (2);
      procedure Set (Value : Integer);
   end P1;

   Data : Integer := 0 with Part_Of => P1;

   protected P2 is
      pragma Priority (3);
      procedure Set (Value : Integer);
   end P2;

   task type TT is
      pragma Priority (1);
   end TT;

   T1, T2 : TT;

end Protected_Sequence;
