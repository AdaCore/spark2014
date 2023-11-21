with External_Util;

package body External with SPARK_Mode is
   function F (X : T) return Boolean is (External_Util (X));
end;
