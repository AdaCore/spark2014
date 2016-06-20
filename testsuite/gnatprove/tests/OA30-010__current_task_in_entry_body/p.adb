with Ada.Task_Identification; use Ada.Task_Identification;
with Q;

package body P is
   procedure S1 is
      T : Task_Id;
   begin
      Q.S2 (T);
   end S1;
end P;
