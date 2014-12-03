with T;

use type T.Input_T;

package body A
is

   pragma SPARK_Mode (On);

   procedure Get (
      X : in     T.Input_T;
      Y :    out T.Output_T)
   is
      L : constant := 7.3526e6;

      H : Float;
   begin
      if X /= 0 then

         --# check X >= 1;
         pragma Assert (Float(X) >= 0.9);
         H := L / Float (X);

         if H >= Float (T.Output_T'Last) then
            Y := T.Output_T'Last;
         else
            pragma Assert (H >= 0.0);
            Y := T.Output_T (H);
         end if;

      else
         Y := 0.0;
      end if;
   end Get;

end A;

