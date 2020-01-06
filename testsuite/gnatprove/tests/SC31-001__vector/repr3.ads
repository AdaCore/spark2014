pragma SPARK_Mode (On);

with Repr2; use Repr2;

package Repr3 
is 
   
   use Vec;
   X : vec_t := To_Vector(New_Item => S.To_Bounded_String(""), Length => 0);

end Repr3;
