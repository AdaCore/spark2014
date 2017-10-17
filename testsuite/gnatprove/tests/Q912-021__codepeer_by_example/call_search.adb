with Assign_Arr; use Assign_Arr;
with Search;
procedure Call_Search (X : in Arr; Y : in Integer; U, V : out Integer) is
begin
   U := Search (X, Y);
   V := Search (X, Y);
end Call_Search;
