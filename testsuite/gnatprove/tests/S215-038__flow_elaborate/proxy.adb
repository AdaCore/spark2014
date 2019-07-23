with P;

function Proxy return Integer is
begin
   return P.Read_From_State;
end;
