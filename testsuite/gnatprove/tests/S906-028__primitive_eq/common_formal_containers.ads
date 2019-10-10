with Ada.Containers.Formal_Vectors;
with Ada.Containers.Formal_Ordered_Sets;

with No_SPARK_Mode; use No_SPARK_Mode;

package Common_Formal_Containers with SPARK_Mode is

   package Int64_Vects is new Ada.Containers.Formal_Vectors
     (Index_Type   => Natural,
      Element_Type => Int64);

   Int64_Vects_Common_Max_Capacity : constant := 200; -- arbitrary

   subtype Int64_Vect is Int64_Vects.Vector (Int64_Vects_Common_Max_Capacity);

   function Int64_Hash (X : Int64) return Ada.Containers.Hash_Type is
     (Ada.Containers.Hash_Type'Mod (X));

--     pragma Assertion_Policy (Post => Ignore);
--     package Int64_Sets is new Ada.Containers.Formal_Hashed_Sets
--       (Element_Type => Int64,
--        Hash         => Int64_Hash);
   package Int64_Sets is new Ada.Containers.Formal_Ordered_Sets
     (Element_Type => Int64);
--     pragma Assertion_Policy (Post => Suppressible);

   Int64_Sets_Common_Max_Capacity : constant := 200; -- arbitrary, and shared among all instances but not necessarily

--     subtype Int64_Set is Int64_Sets.Set
--       (Int64_Sets_Common_Max_Capacity, Int64_Sets.Default_Modulus (Int64_Sets_Common_Max_Capacity));
   subtype Int64_Set is Int64_Sets.Set
     (Int64_Sets_Common_Max_Capacity);

end Common_Formal_Containers;
