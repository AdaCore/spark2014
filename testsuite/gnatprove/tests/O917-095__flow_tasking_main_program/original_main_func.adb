with P;
with PT;

function Original_Main_Func return Integer is
begin
   return (if P.X then 0 else 1);
end;
