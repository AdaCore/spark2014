with Assign_Arr; use Assign_Arr;
procedure Map (X : in Arr; Y : in Integer; Z : out Arr) is
begin
   for J in X'Range loop
      Z (J) := X (J) + Y;
   end loop;
end Map;
