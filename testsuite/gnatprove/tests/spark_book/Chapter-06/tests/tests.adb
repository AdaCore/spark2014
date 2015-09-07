with Ada.Text_IO; use Ada.Text_IO;

with Very_Longs.Test;

procedure Tests is
begin
   Put_Line("Executing Very_Long Tests");
   Very_Longs.Test.Execute;
end Tests;
