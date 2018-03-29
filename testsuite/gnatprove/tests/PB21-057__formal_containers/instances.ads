pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy(Sequential);

with ada.Containers.Formal_Doubly_Linked_Lists;
with ada.Containers.Formal_Vectors;
use Ada.Containers;

package Instances
with SPARK_Mode
is

   subtype Indexes is Count_Type range 1 .. 1000;
   package Lists is new Ada.Containers.Formal_Doubly_Linked_Lists(Integer);
   package Vectors is new Ada.Containers.Formal_Vectors(Indexes, Integer);

   use Vectors;

   procedure Fold_Lasts (V : in out Vectors.Vector)
     with Pre => Length (V) >= 2,
          Post => Length (V) = Length (V)'Old - 1;

   protected Data is
      procedure Push (V : Integer);
      procedure Add (V : Integer);
   private
      Vect : Vectors.Vector(10);
   end Data;

   task type T;


   Arr : array (1 .. 3) of Instances.T;

end Instances;
