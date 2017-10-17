with Unknown;
procedure Call_Unknown_Rel (X : out Integer; Y : in Integer) is
begin
   Unknown (X, Y);
   pragma Assert (X < 2 * Y + 1);
end Call_Unknown_Rel;
