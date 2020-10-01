with Interfaces; use Interfaces;

package body P
  with SPARK_Mode => On
is
   -----------------
   -- Sqrt_Binary --
   -----------------

   function Sqrt_Binary (X : in Sqrt_Domain) return Sqrt_Range is
      subtype Upper_Guess is Integer range 0 .. Sqrt_Range'Last + 1;
      Lower : Sqrt_Range  := 0;
      Upper : Upper_Guess := Upper_Guess'Last;
   begin
      loop
         pragma Loop_Invariant (Lower * Lower <= X);
         pragma Loop_Invariant (Big (X) < Big (Upper) * Big (Upper));
         pragma Loop_Variant (Decreases => Upper - Lower);

         exit when Lower + 1 = Upper;
         declare
            Middle : constant Sqrt_Range := (Lower + Upper) / 2;
         begin
            if Middle * Middle > X then
               Upper := Middle;
            else
               Lower := Middle;
            end if;
         end;
      end loop;

      return Lower;
   end Sqrt_Binary;

   ----------------------
   -- Sqrt_Von_Neumann --
   ----------------------

--  Algorithm from Warren'a "Hacker's Delight" Figure 11.4
--  int isqrt4(unsigned x) {
--     unsigned m, y, b;
--     m = 0x40000000;
--     y = 0;
--     while(m != 0) {              // Do 16 times.
--        b = y | m;
--        y = y >> 1;
--        if (x >= b) {
--           x = x - b;
--           y = y | m;
--        }
--        m = m >> 2;
--     }
--     return y;
--  }

   function Sqrt_Von_Neumann (X : in Sqrt_Domain) return Sqrt_Range is
      subtype U64 is Interfaces.Unsigned_64;
      use type Interfaces.Unsigned_64;
      UX, M, Y, B : U64;

     --  Ghost entities:

      I : U64 := 0 with Ghost;

   begin
      UX := U64 (X);
      pragma Assert (UX <= 2 ** 31 - 1);
      M  := 16#4000_0000#;
      Y  := 0;

      while (M /= 0) loop
         I := I + 1;
         B := Y or M;
         Y := Y / 2;
         if (UX >= B) then
            UX := UX - B;
            Y  := Y or M;
         end if;

         declare
            Bits    : U64 := 32 - 2 * I with Ghost;
            Left_X  : U64 := Shift_Right (U64 (X), Integer(Bits)) with Ghost;
            Left_Y  : U64 := Shift_Right (Y, Integer(Bits)) with Ghost;
            Left_UX : U64 := Shift_Right (UX, Integer(Bits)) with Ghost;
         begin
            pragma Loop_Invariant (I in 1 .. 16);
            pragma Loop_Invariant (M = 2 ** Integer(32 - 2 * I));
            pragma Loop_Invariant (Y mod M = 0);
            pragma Loop_Invariant (Left_Y < 2 ** Integer(I));
            pragma Loop_Invariant (UX mod M = U64 (X) mod M);
            pragma Loop_Invariant (Left_UX = Left_X - Left_Y * Left_Y);
            pragma Loop_Invariant (Left_Y * Left_Y <= Left_X);
            pragma Loop_Invariant (U64(Left_Y + 1) * U64(Left_Y + 1) > U64(Left_X));
         end;
         M := M / 4;
      end loop;

      return Sqrt_Range (Y);
   end Sqrt_Von_Neumann;

end P;
