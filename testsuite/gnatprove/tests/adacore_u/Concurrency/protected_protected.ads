package Protected_Protected
  with SPARK_Mode
is
   protected P is
      procedure Set (Value : Integer);
   end P;

   Data : Integer := 0 with Part_Of => P;

   task type TT;

   T1, T2 : TT;

end Protected_Protected;
