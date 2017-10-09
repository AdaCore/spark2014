pragma SPARK_Mode (On);

with Bounded_Dynamic_Arrays;

package Bounded_Dynamic_Strings is new Bounded_Dynamic_Arrays
  (Component  => Character,
   List_Index => Positive,
   List       => String,
   Default_Value => ' ');
