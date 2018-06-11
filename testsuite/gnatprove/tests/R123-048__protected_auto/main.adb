pragma SPARK_Mode (On);
pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

with P;

procedure Main is
   X : constant Integer := P.PO.F;
   --  F is not in SPARK; this call should be rejected
begin
   pragma Assert (X = 0);
end;
