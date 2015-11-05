with Gene;
with Gene2;

procedure Main is
   package P is new Gene (Integer, 1);
   procedure P2 is new Gene2.P (Integer, 1);
   Z : Integer := 2;
begin
   P.P (Z);
   P2 (Z);
end Main;
