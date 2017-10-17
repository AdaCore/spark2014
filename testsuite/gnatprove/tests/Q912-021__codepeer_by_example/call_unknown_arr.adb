with Assign_Arr; use Assign_Arr;
with Unknown_Arr;
procedure Call_Unknown_Arr (X : in out Arr) is
begin
   X (1) := 1;
   X (4) := 2;
   Unknown_Arr (X);
end Call_Unknown_Arr;
