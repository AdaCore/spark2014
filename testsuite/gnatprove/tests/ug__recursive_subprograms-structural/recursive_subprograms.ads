with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

package Recursive_Subprograms with SPARK_Mode is
   type Cell;
   type List is access Cell;
   type Cell is record
      Value : Integer;
      Next  : List;
   end record;

   function Length (L : List) return Big_Natural is
     (if L = null then Big_Natural'(0) else Length (L.Next) + 1)
   with Subprogram_Variant => (Structural => L);
end Recursive_Subprograms;
