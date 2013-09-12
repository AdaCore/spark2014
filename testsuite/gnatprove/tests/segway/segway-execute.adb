with Segway; use Segway;

package body Segway.Execute is

   -------------
   -- Execute --
   -------------

   procedure Execute (Read : Reader) is
      pragma SPARK_Mode (Off);
      I : Input;
   begin
      loop
         I := Read.all;
         exit when I = No_Input;
         State_Update (I);
      end loop;
      Halt;
   end Execute;

end Segway.Execute;
