package Task_And_PO_Arrays is

   type Task_Id is (A,B,C);

   task type T (Id : Task_Id := A);

   protected type PT is
      entry Dummy;
   end;

   POs : array (Task_Id) of PT;
   Ts  : array (Task_Id) of T;

end;
