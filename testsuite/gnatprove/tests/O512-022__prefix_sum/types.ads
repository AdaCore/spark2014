package Types is pragma SPARK_Mode (On);
   subtype Index is Natural range 0 .. 7;
   type Input is array (Index) of Integer;
end Types;

