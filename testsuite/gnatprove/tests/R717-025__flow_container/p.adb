with SPARK.Containers.Formal.Ordered_Sets;

package body P with Refined_State => (S => Set), SPARK_Mode => On
is

   function Less_Than (Left, Right : T) return Boolean is (Left < Right)
   with Global => null;

   package Sets is new SPARK.Containers.Formal.Ordered_Sets
     (Element_Type => T,
      "<"          => Less_Than);

   Set : Sets.Set (Capacity => 200);

   procedure Add (X : T) with Refined_Global => (In_Out => Set)
   is
   begin
      Sets.Include (Set, X);
   end Add;

end P;
