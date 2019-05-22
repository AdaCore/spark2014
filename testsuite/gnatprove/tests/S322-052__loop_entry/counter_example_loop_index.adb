with Interfaces;
use Interfaces;

package body Counter_Example_Loop_Index
with SPARK_Mode
is

   procedure P is
      K : Natural := 0;
   begin
      for I in 1 .. 100 loop
         K := I;
         pragma Loop_Invariant (K = K'Loop_Entry); --@LOOP_INVARIANT_PRESERV:FAIL
      end loop;
   end P;

end Counter_Example_Loop_Index;
