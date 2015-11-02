with Ada.Task_Identification; use Ada.Task_Identification;

package body P is

   function Dummy return Boolean is
      Me : constant Task_Id := Current_Task;
   begin
      return Me /= Null_Task_Id;
   end;

end;
