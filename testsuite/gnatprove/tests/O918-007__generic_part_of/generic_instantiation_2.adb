package body Generic_Instantiation_2
with
   SPARK_Mode => On,
   Refined_State => (State => GPI.State)
is

   procedure Write (Value : Natural) is
   begin
      GPI.Write (Value);
   end Write;

end Generic_Instantiation_2;
