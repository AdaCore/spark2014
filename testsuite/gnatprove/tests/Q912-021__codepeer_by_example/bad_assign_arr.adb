with Assign_Arr; use Assign_Arr;
procedure Bad_Assign_Arr (X : out Arr; Y : in Integer) is
begin
   X (Y) := 1;
   X (Y + 10) := -1;
end Bad_Assign_Arr;
