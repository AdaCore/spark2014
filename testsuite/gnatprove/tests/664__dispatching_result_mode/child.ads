with Root;
package Child with SPARK_Mode is

   --  Deriving Root should keep Make/Make3 outside SPARK, there should be no
   --  error on the wrapper.

   type T is new Root.T with null record;

   --  Erroneous: Make2 is outside SPARK for [Child.]T

   function Make3 return T is (Make2);

   type GrandChild is new T with null record;

   --  Erroneous: Make2 is still outside SPARK for GrandChild.

   function Make4 return GrandChild is (Make2);

end Child;
