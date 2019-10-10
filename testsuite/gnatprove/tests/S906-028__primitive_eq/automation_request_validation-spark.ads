with No_SPARK_Mode; use No_SPARK_Mode;
with Automation_Request_Validation; use Automation_Request_Validation;
with SPARK_Boundary; use SPARK_Boundary;
with Common_Formal_Containers; use Common_Formal_Containers;

package Automation_Request_Validation.SPARK with SPARK_Mode is


   function All_Elements_In (V : Int64_Vect; S : Int64_Set) return Boolean is
     (for all J in Int64_Vects.First_Index (V) .. Int64_Vects.Last_Index (V)
      => Int64_Sets.Contains (S, Int64_Vects.Element (V, J)))
   with Ghost;

   function Check_For_Required_Operating_Region_And_Keepin_Keepout_Zones
     (Operating_Region  : Int64;
      Operating_Regions : Operating_Region_Maps;
      KeepIn_Zones_Ids  : Int64_Set;
      KeepOut_Zones_Ids : Int64_Set) return Boolean
   is
      -- check for required operating region and keepin/keepout zones
     (if Operating_Region /= 0
      then Int64_Operating_Region_Maps.Contains
        (Operating_Regions, Operating_Region)
      and then All_Elements_In
        ((Int64_Operating_Region_Maps.Element
                  (Operating_Regions, Operating_Region).KeepInAreas),
         KeepIn_Zones_Ids)
      and then All_Elements_In
        ((Int64_Operating_Region_Maps.Element
                  (Operating_Regions, Operating_Region).KeepOutAreas),
         KeepOut_Zones_Ids))
   with Ghost;
end Automation_Request_Validation.SPARK;
