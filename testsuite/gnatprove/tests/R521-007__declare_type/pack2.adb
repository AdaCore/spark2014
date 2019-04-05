package body PACK2 with SPARK_Mode is
   procedure Dummy is null;
begin
   pragma SPARK_Mode (On);
   declare
      type CHILD5 is access Integer;
   begin
      null;
   end;
end PACK2;
