pragma SPARK_Mode (On);

with Total;
package Main is

   function Get
     (Data    : in Total.Enum)
      return Total.Enum;

end Main;
