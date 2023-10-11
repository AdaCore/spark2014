with Imported_Return_Util;

package body Imported_Return with SPARK_Mode is
   function F (X : T) return Boolean is (Imported_Return_Util = X);
end;
