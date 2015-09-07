pragma SPARK_Mode (On);
package Lights is
   type Color_Type is (Red, Yellow, Green);

   function Next_Color (Current_Color : in Color_Type) return Color_Type;

end Lights;
