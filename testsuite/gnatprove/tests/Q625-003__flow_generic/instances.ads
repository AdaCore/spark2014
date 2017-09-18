with A_Package; use A_Package; pragma Elaborate_All (A_Package);

package Instances
with SPARK_Mode => On
is

   procedure A_Null_Procedure (A : in out Integer);

   procedure Procedure_Instance is new A_Generic_Procedure (A_Null_Procedure);

end Instances;
