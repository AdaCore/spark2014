pragma SPARK_Mode (On);

package Exprfun_Array is
   type Ar is array (Integer range <>) of Integer;
   function Empty (A : Ar) return Boolean is (A'First > A'Last);
end Exprfun_Array;
