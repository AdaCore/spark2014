package Tagged_Aggregate_With_Root with SPARK_Mode is
   type Root is tagged record
      F1 : Natural := 0;
   end record;

   type Child1 is new Root with null record;

   type Child2 is new Root with record
      F2 : Natural := 0;
   end record;

   procedure Use_Aggregates;
end Tagged_Aggregate_With_Root;
