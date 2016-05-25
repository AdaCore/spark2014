------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                               R A N D O M                                --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2016, Altran UK Limited              --
--                                                                          --
-- SPARK is free software;  you can  redistribute it and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion. SPARK is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
--                                                                          --
------------------------------------------------------------------------------
--
--  This is an implementation of mersenne twister (2002) version.
--  See http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/MT2002/emt19937ar.html

package body Random with
   SPARK_Mode
is

   function To_State (S : State_Range) return Unsigned_32 is (Unsigned_32 (S));
   function To_State (S : Natural) return Unsigned_32 is (Unsigned_32 (S));

   -----------
   -- Reset --
   -----------

   function Reset (Initiator : Unsigned_32) return Generator is
      Current : Unsigned_32 := Initiator;
      Last    : Unsigned_32;
   begin
      return G : Generator do
         G.Index := 0;
         for I in State_Range loop
            if I > State_Range'First then
               Last    := Current;
               Current := 1812433253 * (Last xor Shift_Right (Last, 30)) +
                            To_State (I);
            end if;
            G.State (I) := Current;
         end loop;
      end return;
   end Reset;

   function Reset (Initiator : Initialization_Vector) return Generator is
      I : State_Range := 1;
      J : Natural     := 0;
   begin
      return G : Generator := Reset (19650218) do
         for K in Long_Long_Integer
           range 1 .. Long_Long_Integer'Max (N, Initiator'Length)
         loop
            G.State (I) :=
              (G.State (I) xor
                 ((G.State (I - 1) xor
                     Shift_Right (G.State (I - 1), 30)) * 1664525))
              + Initiator (J) + To_State (J);
            if I = State_Range'Last then
               G.State (0) := G.State (State_Range'Last);
               I           := 1;
            else
               I           := I + 1;
            end if;
            J := (if J = Initiator'Last then 0 else J + 1);
            pragma Loop_Invariant (I > 0 and J in Initiator'Range);
         end loop;

         for K in State_Range range 1 .. State_Range'Last loop
            G.State (I) :=
              (G.State (I) xor
                 ((G.State (I - 1) xor
                     Shift_Right (G.State (I - 1), 30)) * 1566083941))
              - To_State (I);
            if I = State_Range'Last then
               G.State (0) := G.State (State_Range'Last);
               I           := 1;
            else
               I           := I + 1;
            end if;
            pragma Loop_Invariant (I > 0);
         end loop;

         G.State (0) := 16#80000000#;
      end return;
   end Reset;

   ------------
   -- Random --
   ------------

   procedure Random (G     : in out Generator;
                     Value :    out Unsigned_32)
   is
      function Next (X : State_Range) return State_Range
      is (if X = State_Range'Last
          then State_Range'First
          else X + 1);

      Mat   : constant array (Unsigned_32 range 0 .. 1) of Unsigned_32 :=
        (0, 16#9908b0df#);
      Upper_Mask : constant Unsigned_32 := 16#80000000#;
      Lower_Mask : constant Unsigned_32 := 16#7fffffff#;
   begin
      --  The original code generates these numbers in batches; but we'll
      --  get more constant performance (albeit slower overall, since the
      --  compiler won't be able to vectorize anything) if we just do it
      --  one-at-a-time.
      Value := (G.State (G.Index) and Upper_Mask) or
               (G.State (Next (G.Index)) and Lower_Mask);
      G.State (G.Index) := G.State (case G.Index is
                                    when 0 .. N - M - 1 => G.Index + M,
                                    when N - M .. N - 2 => G.Index + (M - N),
                                    when N - 1          => M - 1);
      G.State (G.Index) := G.State (G.Index) xor
                           Shift_Right (Value, 1) xor
                           Mat (Value and 1);

      Value   := G.State (G.Index);
      G.Index := Next (G.Index);

      Value := Value xor Shift_Right (Value, 11);
      Value := Value xor (Shift_Left (Value, 7) and 16#9d2c5680#);
      Value := Value xor (Shift_Left (Value, 15) and 16#efc60000#);
      Value := Value xor Shift_Right (Value, 18);
   end Random;

end Random;
