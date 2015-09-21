with Generic_Package;
pragma Elaborate_All (Generic_Package);

package Generic_Instantiation_2
with
   SPARK_Mode => On,
   Abstract_State => (State)
is

   procedure Write (Value : Natural)
   with
      Global => (Output => State);

private

   package GPI is new Generic_Package (Natural)
     with Part_Of => State;

end Generic_Instantiation_2;
