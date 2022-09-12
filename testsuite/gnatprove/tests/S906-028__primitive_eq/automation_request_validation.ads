with No_SPARK_Mode; use No_SPARK_Mode;
with SPARK.Containers.Formal.Hashed_Maps;
with SPARK_Boundary; use SPARK_Boundary;
with Common_Formal_Containers; use Common_Formal_Containers;

package Automation_Request_Validation is

   package Int64_Operating_Region_Maps is new SPARK.Containers.Formal.Hashed_Maps
     (Key_Type     => Int64,
      Element_Type => OperatingRegionAreas,
      Hash         => Int64_Hash);

   Operating_Region_Maps_Max_Capacity : constant := 200; -- arbitrary

   subtype Operating_Region_Maps is Int64_Operating_Region_Maps.Map
     (Operating_Region_Maps_Max_Capacity,
      Int64_Operating_Region_Maps.Default_Modulus (Operating_Region_Maps_Max_Capacity));

end Automation_Request_Validation;
