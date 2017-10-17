with Call_Unknown;
procedure Above_Call_Unknown (X : out Integer) is
begin
   Call_Unknown (X);
   pragma Assert (X /= 10);
end Above_Call_Unknown;
