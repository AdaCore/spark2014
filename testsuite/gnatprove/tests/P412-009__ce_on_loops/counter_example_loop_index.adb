with Interfaces;
use Interfaces;

package body Counter_Example_Loop_Index
with SPARK_Mode
is

   procedure P is
      J : Natural := 0;
      K : Natural := 0;
   begin
      for I in 1 .. 100 loop
         K := I;
         pragma Loop_Invariant (J = 0); --@LOOP_INVARIANT_PRESERV:FAIL
         J := I;
      end loop;
   end P;

end Counter_Example_Loop_Index;
