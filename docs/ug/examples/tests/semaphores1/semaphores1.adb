package body Semaphores1 with
  SPARK_Mode
is
   Max_Accounts : constant Natural := 100;

   protected Protected_Natural with Priority => 7 is
      entry Incr;
      function Get return Natural;
   private
      The_Data : Natural := 0;
      Not_Full : Boolean := True;
   end Protected_Natural;

   protected body Protected_Natural is
      entry Incr when Not_Full is
      begin
         The_Data := The_Data + 1;
         if The_Data = Max_Accounts then
            Not_Full := False;
         end if;
      end Incr;

      function Get return Natural is (The_Data);
   end Protected_Natural;

   procedure Initialize_Shared_Data is
   begin
      Protected_Natural.Incr;
   end Initialize_Shared_Data;

   task body T1 is
   begin
      Initialize_Shared_Data;
      Set_True (Semaphore);
      loop
         null;
      end loop;
   end T1;

   task body T2 is
   begin
      Suspend_Until_True (Semaphore);
      loop
         declare
            Tmp : Natural := Protected_Natural.Get;
         begin
            null;
         end;
      end loop;
   end T2;
end Semaphores1;
