with Ada.Task_Identification; use Ada.Task_Identification;

package body Call_From_Sub_In_PT is

   protected body PT is
      entry E when Flag is
      begin
         Proc (T);
      end E;

      procedure Proc (T : out Task_Id) is
      begin
         T := Current_Task;
      end Proc;
   end PT;

begin
   null;
end Call_From_Sub_In_PT;
