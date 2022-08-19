with SPARK.Containers.Formal.Ordered_Maps;
with Test_Map;

procedure Test is
   package Maps is new SPARK.Containers.Formal.Ordered_Maps
     (Positive, Natural);
   use Maps;

   M : Map (10);
begin
   --  Insert code here.
   Test_Map.Test_Ordered_Map;
   Test_Map.Large_Test;
   null;
end Test;
