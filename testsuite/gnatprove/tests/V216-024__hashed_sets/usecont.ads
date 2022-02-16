pragma SPARK_Mode;
with Ada.Containers.Formal_Hashed_Sets;
use Ada.Containers;

package Usecont is

   type R is record
     C : Boolean;
   end record
     with Relaxed_Initialization;

   function Hash (X : Integer) return Hash_Type is (Hash_Type (X));
   package H is new Ada.Containers.Formal_Hashed_Sets (Integer, Hash);

end Usecont;
