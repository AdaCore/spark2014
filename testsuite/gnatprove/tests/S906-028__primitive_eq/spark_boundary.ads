with Common_Formal_Containers; use Common_Formal_Containers;

package SPARK_Boundary with SPARK_Mode is
   pragma Annotate (GNATprove, Terminating, SPARK_Boundary);

   type OperatingRegionAreas is record
      KeepInAreas  : Int64_Vect;
      KeepOutAreas : Int64_Vect;
   end record;

end SPARK_Boundary;
