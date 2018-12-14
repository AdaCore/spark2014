package Foo with Spark_Mode is

   type Potato_Kind is (Picasso, Russet, Laura);

   subtype Potato_Size_Limit is Float range -15.0 .. 10.0;

   type Potato_Shape is record
      Size_Demand_Min : Potato_Size_Limit;
      Size_Demand_Max : Potato_Size_Limit;
   end record;

   type Paramters_T is array (Potato_Kind) of Potato_Shape;

   type Potato_Metrics_T is record
      Parameters : Paramters_T;
   end record;

   procedure Potato
     (Metrics : in     Potato_Metrics_T;
      Max     :    out Potato_Size_Limit;
      Min     :    out Potato_Size_Limit)
   with
     Post =>
       (for all P of Metrics.Parameters =>
          P.Size_Demand_Max <= Max);
   --  Removing this post makes the crash go away.

end Foo;
