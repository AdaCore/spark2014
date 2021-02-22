with Ada.Synchronous_Task_Control; use Ada.Synchronous_Task_Control;

package body Synchronous_Abstractions with SPARK_Mode,
  Refined_State => (Synchronous_State => (P,V,S), Normal_State => T)
is
   task T;
   protected P is
      function Read return Natural;
   private
      V : Natural := 0;
   end P;

   S : Suspension_Object;
   V : Natural := 0 with Atomic, Async_Readers, Async_Writers;

   protected body P is
      function Read return Natural is (V);
   end P;

   procedure Do_Something is
   begin
      Suspend_Until_True (S);
   end Do_Something;

   task body T is
      R : Natural := P.Read;
      VV : Natural := V;
   begin
      V := R;
      loop
         null;
      end loop;
   end T;
end Synchronous_Abstractions;
