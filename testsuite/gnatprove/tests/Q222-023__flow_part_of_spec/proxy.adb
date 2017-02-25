with P;

function Proxy return Integer with SPARK_Mode => Off is
begin
   return P.Expose;
end;
