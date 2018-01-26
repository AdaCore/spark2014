package Types is pragma SPARK_Mode (On);
   subtype Index is Positive range 1 .. 1_000;
   type Text is array (Index) of Integer;
end Types;
