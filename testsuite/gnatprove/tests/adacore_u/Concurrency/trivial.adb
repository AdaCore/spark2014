with Ada.Task_Identification; use Ada.Task_Identification;

package body Trivial
  with SPARK_Mode
is
   Id : Task_Id;

   task body T is
   begin
      loop
         Id := Current_Task;
      end loop;
   end T;
end Trivial;
