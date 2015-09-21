generic
   type Element_T is private;
package Generic_Package
with
   Abstract_State => (State),
   SPARK_Mode => On
is

   procedure Read (Value : out Element_T)
   with
      Global => (Input => State);

   procedure Write (Value: in Element_T)
   with
      Global => (Output => State);

end Generic_Package;
