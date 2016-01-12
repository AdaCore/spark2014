with A;
with BT.O;

package F
is
   type R1 is record
      F1 : A.OS;
   end record;

   function V (X : in R1) return Boolean
   with Post => V'Result = (BT.O.SF (X.F1) = 2);
end F;
