package body Foo with Spark_Mode is

   procedure Potato
     (Metrics : in     Potato_Metrics_T;
      Max     :    out Potato_Size_Limit;
      Min     :    out Potato_Size_Limit)
   is
   begin
      Max := Metrics.Parameters (Potato_Kind'First).Size_Demand_Max;
      Min := Metrics.Parameters (Potato_Kind'First).Size_Demand_Min;
      for I in Potato_Kind
        range Potato_Kind'Succ (Potato_Kind'First) .. Potato_Kind'Last
      loop
         Max := Potato_Size_Limit'Max
           (Max,
            Metrics.Parameters (I).Size_Demand_Max);

         Min := Potato_Size_Limit'Min
           (Min,
            Metrics.Parameters (I).Size_Demand_Min);
      end loop;
   end Potato;

end Foo;
