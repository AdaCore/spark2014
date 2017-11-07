with Ada.Text_IO; use Ada.Text_IO;

procedure Version_3 is
   procedure Local is
   begin
      null;
   end Local;
begin
   Put_Line("Local'Version = """ & Local'Version & """");
   Put_Line("Local'Body_Version = """ & Local'Body_Version & """");
end Version_3;
