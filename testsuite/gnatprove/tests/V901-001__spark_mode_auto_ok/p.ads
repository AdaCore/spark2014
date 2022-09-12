pragma SPARK_Mode (Auto);

with Ada.Finalization;

package P is

   type Bad is new Ada.Finalization.Controlled with null record;

   type Good is new Integer;

end P;
