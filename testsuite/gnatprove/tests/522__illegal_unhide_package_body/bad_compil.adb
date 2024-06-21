package body Bad_Compil with SPARK_Mode is
   pragma Annotate (GNATprove, Unhide_Info, "Package_Body");
   function Id (X : Integer) return Integer is (X);
end Bad_Compil;
