with Ada.Task_Identification;

procedure Main is
   Terminated : Boolean;
   Callable   : Boolean;
begin
   Terminated := Ada.Task_Identification.Is_Terminated (Ada.Task_Identification.Null_Task_Id);
   Callable   := Ada.Task_Identification.Is_Callable   (Ada.Task_Identification.Null_Task_Id);
end;
