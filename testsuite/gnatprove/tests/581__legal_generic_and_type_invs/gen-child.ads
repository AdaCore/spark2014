generic
package Gen.Child with SPARK_Mode is
   procedure P (X : in out T); --@INVARIANT_CHECK:FAIL

   --  visible instances, invariant checks needed
   procedure Vis_PP is new PP;  --@INVARIANT_CHECK:FAIL
   package Vis_Nested is new Nested;
end Gen.Child;
