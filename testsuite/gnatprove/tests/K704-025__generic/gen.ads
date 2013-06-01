pragma SPARK_Mode (On);
generic
   type T is private;
package Gen is
   function Echo (X : T) return T is (X);
end Gen;
