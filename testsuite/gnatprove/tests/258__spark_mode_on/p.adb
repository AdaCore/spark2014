procedure P is
   procedure Local with SPARK_Mode => On;
   procedure Local is null;
begin
  Local;
end P;
