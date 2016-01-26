with G;

procedure C is

   procedure Dummy is new G.Still_Not_Zero (Integer);

begin
   Dummy (1);
end;
