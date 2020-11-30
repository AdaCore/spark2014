package Util is
   X : constant Integer := 2;

   protected type P is
      entry E_01
        with Max_Queue_Length => X;

      entry E_02
        with Max_Queue_Length => 3;

      entry E_03;

   private
      Flag : Boolean := False;
   end P;

   PO : P;

   task type T_01;
   task type T_02;
   task type T_03;

   T1, T2 : T_01;
   -- OK, Max_Queue_Length = 2

   T3, T4, T5, T6 : T_02;
   -- NOT OK, Max_Queue_Length = 3

   T7, T8, T9 : T_03;
   -- OK, Max_Queue_Length not specified so there is no bound

end Util;
