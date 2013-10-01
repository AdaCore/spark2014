pragma SPARK_Mode (On);

function After_Tax
  (Before_Tax : Natural;
   Rate       : Natural) return Natural is
begin
   return Before_Tax - (Before_Tax * Rate) / 100;
end After_Tax;
