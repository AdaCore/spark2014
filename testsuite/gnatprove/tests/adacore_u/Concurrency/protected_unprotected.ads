package Protected_Unprotected
  with SPARK_Mode
is
   protected P is
      procedure Set (Value : Integer);
   end P;

   task type TT;

   T1, T2 : TT;

end Protected_Unprotected;
