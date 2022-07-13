package Q is
   pragma SPARK_Mode(On);

   procedure Tracing with
     Global   => null,
     Annotate => (GNATprove, Always_Return);
end Q;
