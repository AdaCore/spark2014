with Generic_Package;
pragma Elaborate_All (Generic_Package);

package body Generic_Instantiation
with
   SPARK_Mode => On,
   Refined_State => (State => GPI.State)
is

   package GPI is new Generic_Package (Natural);

   procedure Write (Value : Natural) is
   begin
      GPI.Write (Value);
   end Write;

end Generic_Instantiation;
