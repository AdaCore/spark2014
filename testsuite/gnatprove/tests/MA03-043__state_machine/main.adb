with SM_Types; use SM_Types;
with SM_Using_Case_Expression;
with Ada.Text_IO; Use Ada.Text_IO;

procedure Main is
begin

   Put_Line("Hello");


   SM_Using_Case_Expression.Initialise;
   SM_Using_Case_Expression.Progress_SM(Btn_Pressed);

   Put_Line("Passed");

end Main;
