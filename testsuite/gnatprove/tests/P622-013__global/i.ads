with A.B;
use A.B;

package I with
  SPARK_Mode
is

   function Lire_Data return Boolean renames A.B.Lire_Data;

end I;
