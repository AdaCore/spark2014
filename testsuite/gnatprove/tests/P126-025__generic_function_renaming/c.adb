with G;

procedure C is

   function Dummy is new G.Still_Id (Integer);

   X : Integer := Dummy (0);
begin
   pragma Assert (X = 0);
end;
