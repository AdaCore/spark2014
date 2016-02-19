with G;

procedure C is

   package Dummy is new G.Still_Simple (Integer);

   X : Integer := Dummy.Id (0);
begin
   pragma Assert (X = 0);
end;
