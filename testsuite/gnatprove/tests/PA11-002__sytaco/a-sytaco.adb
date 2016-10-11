with System.Task_Primitives.Operations;

package body Ada.Synchronous_Task_Control with
  SPARK_Mode => Off
is

   protected body Suspension_Object is

      entry Wait when Open is
      begin
         Open := False;
      end Wait;

   end Suspension_Object;

end Ada.Synchronous_Task_Control;
