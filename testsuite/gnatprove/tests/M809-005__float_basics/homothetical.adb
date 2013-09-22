with Ada.Numerics.Elementary_Functions;
use Ada.Numerics.Elementary_Functions;

package body homothetical is

   function adjust2triangle (D, kv, ka : Float) return Float with
     Pre => D /= 0.0 and kv > 0.0 and ka > 0.0,
     Post => adjust2triangle'Result > 0.0 and adjust2triangle'Result <= kv;

   function adjust2triangle(D, kv, ka : Float) return Float is
   begin
      if abs(D) < kv*kv/ka then
         return Sqrt(abs(D)*ka);
      else
         return kv;
      end if;
   end;

   ------------------
   -- homothetical --
   ------------------

   procedure homothetical
     (D : in Joint_Values;
      kv : in Joint_Values;
      ka : in Joint_Values;
      kvmax : out Joint_Values;
      kamax : out Joint_Values)
   is
      -- Velocity ratio of the synchronized trajectory for joint j.
      lambda : Joint_Values := (others => 1.0);

      -- Acceleration ratio of the synchronized trajectory for joint j.
      upsilon : Joint_Values := (others => 1.0);

      -- Maximum achievable velocity.
      -- Fixme: Initialized only to avoid warning in loop invariant.
      kvp : Joint_Values := (others => 0.0);
   begin
      for i in kvp'Range loop
         pragma Loop_Invariant (for all J in kvp'First .. I - 1 =>
                                  kvp (J) > 0.0);

         kvp(i) := adjust2triangle(D(i), kv(i), ka(i));
      end loop;

      kvmax := (others => 0.0);
      kamax := (others => 0.0);

      pragma Assert_And_Cut(for all I in Joint_Index => ka(i) > 0.0
                              and kvp(i) /= 0.0
                              and D(i) /= 0.0);

      for i in Joint_Values'Range loop
         -- lambda and upsilon are pre-initialized

         for j in Joint_Values'Range loop
            if i /= j then
               lambda(i)  := Float'Min(lambda(i), (kvp(j)*abs(D(i)))/(kvp(i)*abs(D(j))));
               upsilon(i) := Float'Min(upsilon(i), (ka (j)*abs(D(i)))/(ka (i)*abs(D(j))));
            end if;
         end loop;

         kvmax(i) := lambda(i)  * kvp(i);
         kamax(i) := upsilon(i) * ka(i);
      end loop;
   end homothetical;

end homothetical;
