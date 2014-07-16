with Unit1; use Unit1;
with Unit2; use Unit2;
with Ada.Text_IO; use Ada.Text_IO;

procedure Main is
   X1 : T1;
   X2 : T2;
begin
   X1.Create;
   pragma Assert (X1.Is_Zero);
   X1.Bump;
   pragma Assert (not X1.Is_Max);

   X2.Create;
   pragma Assert (X2.Is_Zero);
   X2.Bump;
   pragma Assert (not X2.Is_Max);

   Put_Line ("Success!");
end Main;
