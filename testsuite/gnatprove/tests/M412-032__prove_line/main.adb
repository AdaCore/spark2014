with Gene;

procedure Main is
   package P is new Gene (Integer, 1);
   Z : Integer := 2;
begin
   P.P (Z);
end Main;
