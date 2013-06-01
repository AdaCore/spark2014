with Pack;
procedure User is
   package P1 is new Pack (1);
   package P2 is new Pack (2);
begin
   pragma Assert (P1.S = "image of N");
   pragma Assert (P2.S = "image of N");
end User;

