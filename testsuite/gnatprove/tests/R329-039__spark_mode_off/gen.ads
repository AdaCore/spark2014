generic
   V : Integer;
package Gen is
   function Get return Integer;
   function Ok return Integer with SPARK_Mode => On;
   function Bad return Integer with SPARK_Mode => Off;
end Gen;
