with Segway; use Segway;

package body Segway.Execute is
   pragma SPARK_Mode (Off);

   -------------
   -- Execute --
   -------------

   procedure Execute (Read : Reader) is
      I : Input;
   begin
      Initialize;
      loop
         I := Read.all;
         exit when I = No_Input;
         State_Update (I);
      end loop;
      Halt;
   end Execute;

end Segway.Execute;
