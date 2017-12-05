with Ada.Task_Identification; use Ada.Task_Identification;
package Call_From_Sub_In_PT is
   protected type PT is
      entry E;
      procedure Proc (T : out Task_Id);
   private
      D    : Integer := 3;
      T    : Task_Id := Null_Task_Id;
      Flag : Boolean := True;
   end PT;
end;
