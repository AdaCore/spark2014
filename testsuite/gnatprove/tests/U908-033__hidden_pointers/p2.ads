with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;
with P1; use P1;

package P2 is
   type Child is new Object with record
      F : Natural;
      G : Natural;
   end record;

   --  Lemma: Equality on Child is still an equivalence
   function Witness (O : Child) return Big_Integer is
     (To_Big_Integer (O.F) * 2_147_483_648 + To_Big_Integer (O.G));
   function "=" (O1, O2 : Child) return Boolean is
     (O1.F = O2.F and O1.G = O2.G);
end P2;
