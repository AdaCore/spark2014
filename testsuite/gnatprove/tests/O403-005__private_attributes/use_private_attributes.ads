with Private_With_Attributes; use Private_With_Attributes;
with Public_Derives_Private;  use Public_Derives_Private;

package Use_Private_Attributes with SPARK_Mode is
   procedure Test_Constrained (U : in out Private_Unconstrained) with
     Pre => U'Constrained;

   procedure Test_Tag (C : Natural);
end Use_Private_Attributes;
