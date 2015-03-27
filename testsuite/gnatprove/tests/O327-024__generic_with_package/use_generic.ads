with Generic_Packages; use Generic_Packages;

pragma Elaborate_All (Generic_Packages);
package Use_Generic with SPARK_Mode is
   package My_Add is new Gen_Add (Natural);

   type Nat_Array is array (Positive range <>) of Natural;

   package My_Sum is new Gen_Sum (Natural, Nat_Array, My_Add);
end Use_Generic;
