package body Segway.Execute is

   -------------
   -- Execute --
   -------------

   procedure Execute (Read : Reader) is
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
