package P is

   protected type PT is
      entry E1
        with Max_Queue_Length => 5;

      entry E2
        with Max_Queue_Length => 1;

      entry E3;

   end PT;

   PO : PT;

   task type T1;
   task type T2;
   task type T3;
   task type T4;

   TO1, TO2, TO3, TO4 : T1;
   TO5, TO6 : T2;
   T07, TO8, T09, T10 : T3;

end P;
