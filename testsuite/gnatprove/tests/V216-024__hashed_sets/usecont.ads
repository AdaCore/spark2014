pragma SPARK_Mode;
with SPARK.Containers.Formal.Hashed_Sets;
with Ada.Containers; use Ada.Containers;

package Usecont is

   type R is record
     C : Boolean;
   end record
     with Relaxed_Initialization;

   function Hash (X : Integer) return Hash_Type is (Hash_Type (X));
   package H is new SPARK.Containers.Formal.Hashed_Sets (Integer, Hash);

end Usecont;
