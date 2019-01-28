with Ada.Finalization; use Ada.Finalization;
package P with SPARK_Mode is
   type T is tagged limited private;
private
   type T is new Limited_Controlled with null record;
end P;
