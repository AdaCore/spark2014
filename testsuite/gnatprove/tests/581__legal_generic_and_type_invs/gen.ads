generic
package Gen with SPARK_Mode is
  type T is private;

   generic
   procedure PP (X : in out T);

   generic
   package Nested is
      procedure PPP (X : in out T);  --@INVARIANT_CHECK:FAIL
   end Nested;

private
   type T is new Integer with Type_Invariant => T /= 0, Default_Value => 1;
end Gen;
