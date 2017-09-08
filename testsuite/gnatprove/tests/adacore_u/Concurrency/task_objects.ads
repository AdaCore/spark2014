package Task_Objects
  with SPARK_Mode
is
   task T1;

   task type TT;
   T2 : TT;

   type TA is array (1 .. 3) of TT;
   T3 : TA;

   type TR is record
      A, B : TT;
   end record;
   T4 : TR;

end Task_Objects;
