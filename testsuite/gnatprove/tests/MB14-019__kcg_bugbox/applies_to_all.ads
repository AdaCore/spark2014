pragma SPARK_Mode;
-- Tests related to TN K331-010
-- The extension of the accept annotation to include the keyword "all"
-- when used with the profile -language=kcg
package Applies_To_All
is
   procedure Proc_1 (B : in Boolean; X : out Integer)
      with Depends => (X => B);
end Applies_To_All;
