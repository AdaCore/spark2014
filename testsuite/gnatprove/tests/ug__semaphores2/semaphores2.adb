package body Semaphores2 with
  SPARK_Mode
is
   procedure Enter_Protected_Region is
   begin
      --  Interact with some data/user
      null;
   end Enter_Protected_Region;

   task body T1 is
   begin
      loop
         Suspend_Until_True (Semaphore1);
         Enter_Protected_Region;
         Set_True (Semaphore2);
      end loop;
   end T1;

   task body T2 is
   begin
      loop
         Suspend_Until_True (Semaphore2);
         Enter_Protected_Region;
         Set_True (Semaphore1);
      end loop;
   end T2;
end Semaphores2;
