generic
   type T is private;
package Exclude_Generic_Unit_Body with
  SPARK_Mode => On
is
   procedure Process (X : in out T);
end Exclude_Generic_Unit_Body;
