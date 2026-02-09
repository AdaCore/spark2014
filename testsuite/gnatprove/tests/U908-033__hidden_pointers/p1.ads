with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;

package P1 is
   type Object is tagged null record;

   --  Lemma: Equality on Object is an equivalence.
   --  It will need to be proved for each new derivation
   function Witness (O : Object) return Big_Integer is (0);
   function "=" (O1, O2 : Object) return Boolean is
     (True)
   with Post'Class => "="'Result = (Witness (O1) = Witness (O2));
end P1;
