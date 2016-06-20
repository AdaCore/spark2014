with P;
with Ada.Task_Identification; use Ada.Task_Identification;

package Main_Package is
   protected type PT is
      entry E;
   private
      D    : Integer := 3;
      Flag : Boolean := True;
   end PT;
end;
