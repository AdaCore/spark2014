pragma SPARK_Mode(On);

package body union_init is

   procedure init_union (test : out union_test) is
      --local_record : basic_record;
   begin
      --test := (discr => 1 ,field2 => local_record);  --works
      test := (discr => 1 ,field2 => <>);  --crashes
   end init_union;
end union_init;
