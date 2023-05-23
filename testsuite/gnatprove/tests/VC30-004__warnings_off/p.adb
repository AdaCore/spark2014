procedure P (X : in out Integer) is
begin
   pragma Warnings (GNATprove, Off);
   X := 2;
   pragma Warnings (GNATprove, On);
   X := 3;
   X := 4;
end;
