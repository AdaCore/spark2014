with System.Tasking;

with Ada.Task_Identification;

package Ada.Synchronous_Task_Control with
  SPARK_Mode
is
   type Suspension_Object is limited private;

private
   pragma SPARK_Mode (Off);


   protected type Suspension_Object is
      entry Wait;

      pragma Interrupt_Priority;
   private
      Open : Boolean := False;
      --  Status
   end Suspension_Object;

end Ada.Synchronous_Task_Control;
