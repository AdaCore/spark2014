pragma SPARK_Mode (Auto);

with Ada.Finalization;

package P with SPARK_Mode => Auto is

   pragma SPARK_Mode (Auto);

   type Bad is new Ada.Finalization.Controlled with null record;

   type Good is new Integer;

   procedure Local with SPARK_Mode => Auto;

end P;
