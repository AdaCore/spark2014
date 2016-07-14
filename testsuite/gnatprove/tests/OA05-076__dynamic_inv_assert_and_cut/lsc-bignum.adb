-------------------------------------------------------------------------------
-- This file is part of libsparkcrypto.
--
-- Copyright (C) 2011, Stefan Berghofer
-- Copyright (C) 2011, secunet Security Networks AG
-- All rights reserved.
--
-- Redistribution  and  use  in  source  and  binary  forms,  with  or  without
-- modification, are permitted provided that the following conditions are met:
--
--    * Redistributions of source code must retain the above copyright notice,
--      this list of conditions and the following disclaimer.
--
--    * Redistributions in binary form must reproduce the above copyright
--      notice, this list of conditions and the following disclaimer in the
--      documentation and/or other materials provided with the distribution.
--
--    * Neither the name of the author nor the names of its contributors may be
--      used to endorse or promote products derived from this software without
--      specific prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE  COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
-- AND ANY  EXPRESS OR IMPLIED WARRANTIES,  INCLUDING, BUT NOT LIMITED  TO, THE
-- IMPLIED WARRANTIES OF  MERCHANTABILITY AND FITNESS FOR  A PARTICULAR PURPOSE
-- ARE  DISCLAIMED. IN  NO EVENT  SHALL  THE COPYRIGHT  HOLDER OR  CONTRIBUTORS
-- BE  LIABLE FOR  ANY  DIRECT, INDIRECT,  INCIDENTAL,  SPECIAL, EXEMPLARY,  OR
-- CONSEQUENTIAL  DAMAGES  (INCLUDING,  BUT  NOT  LIMITED  TO,  PROCUREMENT  OF
-- SUBSTITUTE GOODS  OR SERVICES; LOSS  OF USE,  DATA, OR PROFITS;  OR BUSINESS
-- INTERRUPTION)  HOWEVER CAUSED  AND ON  ANY THEORY  OF LIABILITY,  WHETHER IN
-- CONTRACT,  STRICT LIABILITY,  OR  TORT (INCLUDING  NEGLIGENCE OR  OTHERWISE)
-- ARISING IN ANY WAY  OUT OF THE USE OF THIS SOFTWARE, EVEN  IF ADVISED OF THE
-- POSSIBILITY OF SUCH DAMAGE.
-------------------------------------------------------------------------------

with Interfaces;

package body LSC.Bignum
is

   procedure Initialize
     (A       :    out Big_Int;
      A_First : in     Natural;
      A_Last  : in     Natural)
   is
   begin
      for I in Natural range A_First .. A_Last
      loop
         pragma Warnings (Off, """A"" may be referenced before it has a value");
         pragma Loop_Invariant
           (for all K in Natural range A_First .. I - 1 => (A (K) = 0));
         pragma Warnings (On, """A"" may be referenced before it has a value");
         pragma Annotate
           (GNATprove, False_Positive,
            """A"" might not be initialized",
            "Initialized between A_First and A_Last");

         A (I) := 0;
      end loop;
   end Initialize;
   pragma Annotate
     (GNATprove, False_Positive,
      """A"" might not be initialized",
      "Initialized between A_First and A_Last");
   pragma Annotate
     (GNATprove, False_Positive,
      """A"" might not be initialized in ""Initialize""",
      "Initialized between A_First and A_Last");

   ----------------------------------------------------------------------------

   procedure Copy
     (A       : in     Big_Int;
      A_First : in     Natural;
      A_Last  : in     Natural;
      B       : in out Big_Int;
      B_First : in     Natural)
   is
   begin
      for I in Natural range A_First .. A_Last
      loop
         pragma Loop_Invariant
           (for all K in Natural range B'Range =>
              ((if K in B_First .. B_First + I - A_First - 1 then
                  B (K) = A (A_First + K - B_First)) and
               (if K not in B_First .. B_First + I - A_First - 1 then
                  B (K) = B'Loop_Entry (K))));

         B (B_First + (I - A_First)) := A (I);

         pragma Assert_And_Cut
           (for all K in Natural range B'Range =>
              ((if K in B_First .. B_First + (I + 1) - A_First - 1 then
                  B (K) = A (A_First + K - B_First)) and
               (if K not in B_First .. B_First + (I + 1) - A_First - 1 then
                  B (K) = B'Loop_Entry (K))));
      end loop;
   end Copy;

   ----------------------------------------------------------------------------

   function Word_Of_Boolean (B : Boolean) return Types.Word32
     with Post =>
       Math_Int.From_Word32 (Word_Of_Boolean'Result) = Num_Of_Boolean (B)
   is
      Result : Types.Word32;
   begin
      if B then
         Result := 1;
      else
         Result := 0;
      end if;

      return Result;
   end Word_Of_Boolean;

   ----------------------------------------------------------------------------

   procedure Sub_Inplace
     (A       : in out Big_Int;
      A_First : in     Natural;
      A_Last  : in     Natural;
      B       : in     Big_Int;
      B_First : in     Natural;
      Carry   :    out Boolean)
   is
      J         : Natural;
      New_Carry : Boolean;
   begin
      Carry := False;

      for I in Natural range A_First .. A_Last
      loop
         pragma Loop_Invariant
           (Num_Of_Big_Int (A'Loop_Entry, A_First, I - A_First) -
            Num_Of_Big_Int (B, B_First, I - A_First) =
            Num_Of_Big_Int (A, A_First, I - A_First) -
            Base ** (I - A_First) * Num_Of_Boolean (Carry) and
            (for all K in Natural range I .. A_Last =>
               (A (K) = A'Loop_Entry (K))));

         J := B_First + (I - A_First);
         New_Carry := A (I) < B (J) or else (A (I) = B (J) and then Carry);
         A (I) := (A (I) - B (J)) - Word_Of_Boolean (Carry);
         Carry := New_Carry;

         pragma Assert_And_Cut
           (Num_Of_Big_Int (A'Loop_Entry, A_First, (I + 1) - A_First) -
            Num_Of_Big_Int (B, B_First, (I + 1) - A_First) =
            Num_Of_Big_Int (A, A_First, (I + 1) - A_First) -
            Base ** ((I + 1) - A_First) * Num_Of_Boolean (Carry) and
            (for all K in Natural range I + 1 .. A_Last =>
               (A (K) = A'Loop_Entry (K))));
      end loop;
   end Sub_Inplace;

   ----------------------------------------------------------------------------

   function Less
     (A       : Big_Int;
      A_First : Natural;
      A_Last  : Natural;
      B       : Big_Int;
      B_First : Natural)
     return Boolean
   is
      J      : Natural;
      Result : Boolean;
   begin
      Result := False;

      for I in reverse Natural range A_First .. A_Last
      loop
         pragma Loop_Invariant
           (Num_Of_Big_Int (A, I + 1, A_Last - I) =
            Num_Of_Big_Int (B, B_First + (I - A_First) + 1, A_Last - I) and
            not Result);

         J := B_First + (I - A_First);

         if A (I) < B (J) then
            Result := True;
            exit;
         end if;

         exit when A (I) > B (J);
      end loop;

      return Result;
   end Less;

   ----------------------------------------------------------------------------

   procedure Single_Add_Mult_Mult
     (A       : in out Types.Word32;
      V       : in     Types.Word32;
      W       : in     Types.Word32;
      X       : in     Types.Word32;
      Y       : in     Types.Word32;
      Carry1  : in out Types.Word32;
      Carry2  : in out Types.Word32)
     with
       Depends =>
         (A =>+ (V, W, X, Y, Carry1),
          (Carry1, Carry2) => (A, V, W, X, Y, Carry1, Carry2)),
       Post =>
         Math_Int.From_Word32 (A'Old) +
         Math_Int.From_Word32 (V) * Math_Int.From_Word32 (W) +
         Math_Int.From_Word32 (X) * Math_Int.From_Word32 (Y) +
         Math_Int.From_Word32 (Carry1'Old) +
         Base * Math_Int.From_Word32 (Carry2'Old) =
         Math_Int.From_Word32 (A) +
         Base * (Math_Int.From_Word32 (Carry1) +
           Base * Math_Int.From_Word32 (Carry2))
   is
      Mult1, Mult2, Temp : Types.Word64;
   begin
      Mult1 := Types.Word64 (V) * Types.Word64 (W);
      Mult2 := Types.Word64 (X) * Types.Word64 (Y);
      Temp :=
        Types.Word64 (A) +
        Types.Word64 (Carry1) +
        (Mult1 and Types.Word64 (Types.Word32'Last)) +
        (Mult2 and Types.Word64 (Types.Word32'Last));
      A := Types.Word32 (Temp and Types.Word64 (Types.Word32'Last));
      Temp :=
        Types.Word64 (Carry2) +
        Interfaces.Shift_Right (Mult1, 32) +
        Interfaces.Shift_Right (Mult2, 32) +
        Interfaces.Shift_Right (Temp, 32);
      Carry1 := Types.Word32 (Temp and Types.Word64 (Types.Word32'Last));
      Carry2 := Types.Word32 (Interfaces.Shift_Right (Temp, 32));
   end Single_Add_Mult_Mult;

   ----------------------------------------------------------------------------

   procedure Add_Mult_Mult
     (A       : in out Big_Int;
      A_First : in     Natural;
      A_Last  : in     Natural;
      B       : in     Big_Int;
      B_First : in     Natural;
      C       : in     Big_Int;
      C_First : in     Natural;
      X       : in     Types.Word32;
      Y       : in     Types.Word32;
      Carry1  : in out Types.Word32;
      Carry2  : in out Types.Word32)
     with
       Depends =>
         ((A, Carry1, Carry2) =>
            (A, A_First, A_Last, B, B_First, C, C_First, X, Y, Carry1, Carry2)),
       Pre =>
         A_First in A'Range and
         A_Last + 1 in A'Range and
         A_First <= A_Last and
         B_First in B'Range and
         B_First + (A_Last - A_First) in B'Range and
         C_First in C'Range and
         C_First + (A_Last - A_First) in C'Range,
       Post =>
         Num_Of_Big_Int (A'Old, A_First + 1, A_Last - A_First + 1) +
         Num_Of_Big_Int (B, B_First, A_Last - A_First + 1) *
         Math_Int.From_Word32 (X) +
         Num_Of_Big_Int (C, C_First, A_Last - A_First + 1) *
         Math_Int.From_Word32 (Y) +
         Math_Int.From_Word32 (Carry1'Old) +
         Base * Math_Int.From_Word32 (Carry2'Old) =
         Num_Of_Big_Int (A, A_First, A_Last - A_First + 1) +
         Base ** (A_Last - A_First + 1) * (Math_Int.From_Word32 (Carry1) +
           Base * Math_Int.From_Word32 (Carry2))
   is
      Temp : Types.Word32;
   begin
      for I in Natural range A_First .. A_Last
      loop
         pragma Loop_Invariant
           (Num_Of_Big_Int (A'Loop_Entry, A_First + 1, I - A_First) +
            Num_Of_Big_Int (B, B_First, I - A_First) *
            Math_Int.From_Word32 (X) +
            Num_Of_Big_Int (C, C_First, I - A_First) *
            Math_Int.From_Word32 (Y) +
            Math_Int.From_Word32 (Carry1'Loop_Entry) +
            Base * Math_Int.From_Word32 (Carry2'Loop_Entry) =
            Num_Of_Big_Int (A, A_First, I - A_First) +
            Base ** (I - A_First) * (Math_Int.From_Word32 (Carry1) +
              Base * Math_Int.From_Word32 (Carry2)) and
            (for all K in Natural range I .. A_Last + 1 =>
               (A (K) = A'Loop_Entry (K))));

         Temp := A (I + 1);
         Single_Add_Mult_Mult
           (Temp,
            B (B_First + (I - A_First)), X,
            C (C_First + (I - A_First)), Y,
            Carry1, Carry2);
         A (I) := Temp;

         pragma Assert_And_Cut
           (Num_Of_Big_Int (A'Loop_Entry, A_First + 1, (I + 1) - A_First) +
            Num_Of_Big_Int (B, B_First, (I + 1) - A_First) *
            Math_Int.From_Word32 (X) +
            Num_Of_Big_Int (C, C_First, (I + 1) - A_First) *
            Math_Int.From_Word32 (Y) +
            Math_Int.From_Word32 (Carry1'Loop_Entry) +
            Base * Math_Int.From_Word32 (Carry2'Loop_Entry) =
            Num_Of_Big_Int (A, A_First, (I + 1) - A_First) +
            Base ** ((I + 1) - A_First) * (Math_Int.From_Word32 (Carry1) +
              Base * Math_Int.From_Word32 (Carry2)) and
            (for all K in Natural range I + 1 .. A_Last + 1 =>
               (A (K) = A'Loop_Entry (K))));
      end loop;
   end Add_Mult_Mult;

   ----------------------------------------------------------------------------

   procedure Mont_Mult
     (A       :    out Big_Int;
      A_First : in     Natural;
      A_Last  : in     Natural;
      B       : in     Big_Int;
      B_First : in     Natural;
      C       : in     Big_Int;
      C_First : in     Natural;
      M       : in     Big_Int;
      M_First : in     Natural;
      M_Inv   : in     Types.Word32)
   is
      Carry : Boolean;
      Carry1, Carry2, A_MSW, BI, U : Types.Word32;
   begin
      Initialize (A, A_First, A_Last);
      A_MSW := 0;

      for I in Natural range A_First .. A_Last
      loop
         pragma Loop_Invariant
           ((Num_Of_Big_Int (A, A_First, A_Last - A_First + 1) +
             Base ** (A_Last - A_First + 1) * Math_Int.From_Word32 (A_MSW)) mod
            Num_Of_Big_Int (M, M_First, A_Last - A_First + 1) =
            (Num_Of_Big_Int (B, B_First, I - A_First) *
             Num_Of_Big_Int (C, C_First, A_Last - A_First + 1) *
             Inverse (Num_Of_Big_Int (M, M_First, A_Last - A_First + 1),
               Base) ** (I - A_First)) mod
            Num_Of_Big_Int (M, M_First, A_Last - A_First + 1) and
            Num_Of_Big_Int (A, A_First, A_Last - A_First + 1) +
            Base ** (A_Last - A_First + 1) * Math_Int.From_Word32 (A_MSW) <
            Math_Int.From_Word32 (2) *
            Num_Of_Big_Int (M, M_First, A_Last - A_First + 1) -
            Math_Int.From_Word32 (1));

         Carry1 := 0;
         Carry2 := 0;
         BI := B (B_First + (I - A_First));
         U := (A (A_First) + BI * C (C_First)) * M_Inv;
         Single_Add_Mult_Mult
           (A (A_First), BI, C (C_First), M (M_First), U, Carry1, Carry2);
         Add_Mult_Mult
           (A, A_First, A_Last - 1,
            C, C_First + 1, M, M_First + 1,
            BI, U, Carry1, Carry2);
         A (A_Last) := A_MSW + Carry1;
         A_MSW := Carry2 + Word_Of_Boolean (A (A_Last) < Carry1);

         pragma Assert_And_Cut
           ((Num_Of_Big_Int (A, A_First, A_Last - A_First + 1) +
             Base ** (A_Last - A_First + 1) * Math_Int.From_Word32 (A_MSW)) mod
            Num_Of_Big_Int (M, M_First, A_Last - A_First + 1) =
            (Num_Of_Big_Int (B, B_First, (I + 1) - A_First) *
             Num_Of_Big_Int (C, C_First, A_Last - A_First + 1) *
             Inverse (Num_Of_Big_Int (M, M_First, A_Last - A_First + 1),
               Base) ** ((I + 1) - A_First)) mod
            Num_Of_Big_Int (M, M_First, A_Last - A_First + 1) and
            Num_Of_Big_Int (A, A_First, A_Last - A_First + 1) +
            Base ** (A_Last - A_First + 1) * Math_Int.From_Word32 (A_MSW) <
            Math_Int.From_Word32 (2) *
            Num_Of_Big_Int (M, M_First, A_Last - A_First + 1) -
            Math_Int.From_Word32 (1));
      end loop;

      if A_MSW /= 0 or else
        not Less (A, A_First, A_Last, M, M_First)
      then
         pragma Warnings (Off, "unused assignment to ""Carry""");
         Sub_Inplace (A, A_First, A_Last, M, M_First, Carry);
         pragma Warnings (On, "unused assignment to ""Carry""");
      end if;
   end Mont_Mult;

   ----------------------------------------------------------------------------

   function Bit_Set
     (A       : Big_Int;
      A_First : Natural;
      I       : Types.Word64)
     return Boolean
     with
       Pre =>
         A_First in A'Range and then
         I / 32 <= Types.Word64 (A'Last - A_First),
       Post =>
         Bit_Set'Result =
         ((A (A_First + Natural (I / 32)) and
           2 ** (Natural (I mod 32))) /= 0)
   is
   begin
      return
        (A (A_First + Natural (I / 32)) and
         2 ** (Natural (I mod 32))) /= 0;
   end Bit_Set;

   ----------------------------------------------------------------------------

   procedure Mont_Exp_Window
     (A          :    out Big_Int;
      A_First    : in     Natural;
      A_Last     : in     Natural;
      X          : in     Big_Int;
      X_First    : in     Natural;
      E          : in     Big_Int;
      E_First    : in     Natural;
      E_Last     : in     Natural;
      M          : in     Big_Int;
      M_First    : in     Natural;
      K          : in     Natural;
      Aux1       :    out Big_Int;
      Aux1_First : in     Natural;
      Aux2       :    out Big_Int;
      Aux2_First : in     Natural;
      Aux3       :    out Big_Int;
      Aux3_First : in     Natural;
      Aux4       :    out Big_Int;
      Aux4_First : in     Natural;
      R          : in     Big_Int;
      R_First    : in     Natural;
      M_Inv      : in     Types.Word32)
   is
      J, L, S : Natural;
      I : Types.Word64;
      W : Types.Word32;
   begin
      L := A_Last - A_First;

      Initialize (Aux1, Aux1_First, Aux1_First + L);
      Aux1 (Aux1_First) := 1;

      Mont_Mult
        (Aux3, Aux3_First, Aux3_First + L,
         R, R_First, Aux1, Aux1_First,
         M, M_First, M_Inv);

      Mont_Mult
        (Aux4, Aux4_First, Aux4_First + L,
         X, X_First, R, R_First,
         M, M_First, M_Inv);

      Mont_Mult
        (Aux2, Aux2_First, Aux2_First + L,
         Aux4, Aux4_First, Aux4, Aux4_First,
         M, M_First, M_Inv);

      pragma Assert_And_Cut
        (L = A_Last - A_First and
         Num_Of_Big_Int (Aux1, Aux1_First, L + 1) =
         Math_Int.From_Word32 (1) and
         Num_Of_Big_Int (Aux2, Aux2_First, L + 1) =
         Num_Of_Big_Int (X, X_First, L + 1) *
         Num_Of_Big_Int (X, X_First, L + 1) *
         Base ** (L + 1) mod
         Num_Of_Big_Int (M, M_First, L + 1) and
         Num_Of_Big_Int (Aux3, Aux3_First, L + 1) =
         Base ** (L + 1) mod
         Num_Of_Big_Int (M, M_First, L + 1) and
         Num_Of_Big_Int (Aux4, Aux4_First, L + 1) =
         Num_Of_Big_Int (X, X_First, L + 1) *
         Base ** (L + 1) mod
         Num_Of_Big_Int (M, M_First, L + 1));

      for H in Natural range 1 .. 2 ** K - 1
      loop
         pragma Loop_Invariant
           (L = A_Last - A_First and
            Num_Of_Big_Int (Aux1, Aux1_First, L + 1) =
            Math_Int.From_Word32 (1) and
            Num_Of_Big_Int (Aux2, Aux2_First, L + 1) =
            Num_Of_Big_Int (X, X_First, L + 1) *
            Num_Of_Big_Int (X, X_First, L + 1) *
            Base ** (L + 1) mod
            Num_Of_Big_Int (M, M_First, L + 1) and
            Num_Of_Big_Int (Aux3, Aux3_First, L + 1) =
            Base ** (L + 1) mod
            Num_Of_Big_Int (M, M_First, L + 1) and
            (for all N in Natural range 0 .. H - 1 =>
               (Num_Of_Big_Int (Aux4, Aux4_First + N * (L + 1), L + 1) =
                Num_Of_Big_Int (X, X_First, L + 1) ** (2 * N + 1) *
                Base ** (L + 1) mod
                Num_Of_Big_Int (M, M_First, L + 1))));

         Mont_Mult
           (A, A_First, A_Last,
            Aux4, Aux4_First + (H - 1) * (L + 1), Aux2, Aux2_First,
            M, M_First, M_Inv);

         Copy (A, A_First, A_Last, Aux4, Aux4_First + H * (L + 1));

         pragma Assert_And_Cut
           (L = A_Last - A_First and
            Num_Of_Big_Int (Aux1, Aux1_First, L + 1) =
            Math_Int.From_Word32 (1) and
            Num_Of_Big_Int (Aux2, Aux2_First, L + 1) =
            Num_Of_Big_Int (X, X_First, L + 1) *
            Num_Of_Big_Int (X, X_First, L + 1) *
            Base ** (L + 1) mod
            Num_Of_Big_Int (M, M_First, L + 1) and
            Num_Of_Big_Int (Aux3, Aux3_First, L + 1) =
            Base ** (L + 1) mod
            Num_Of_Big_Int (M, M_First, L + 1) and
            (for all N in Natural range 0 .. H =>
               (Num_Of_Big_Int (Aux4, Aux4_First + N * (L + 1), L + 1) =
                Num_Of_Big_Int (X, X_First, L + 1) ** (2 * N + 1) *
                Base ** (L + 1) mod
                Num_Of_Big_Int (M, M_First, L + 1))));
      end loop;

      I := (Types.Word64 (E_Last - E_First) + 1) * 32 - 1;

      loop
         pragma Loop_Invariant
           (L = A_Last - A_First and
            Num_Of_Big_Int (Aux1, Aux1_First, L + 1) =
            Math_Int.From_Word32 (1) and
            Num_Of_Big_Int (Aux2, Aux2_First, L + 1) =
            Num_Of_Big_Int (X, X_First, L + 1) *
            Num_Of_Big_Int (X, X_First, L + 1) *
            Base ** (L + 1) mod
            Num_Of_Big_Int (M, M_First, L + 1) and
            Num_Of_Big_Int (Aux3, Aux3_First, L + 1) =
            Num_Of_Big_Int (X, X_First, L + 1) **
            (Num_Of_Big_Int (E, E_First, E_Last - E_First + 1) /
             Math_Int.From_Word32 (2) **
               (Math_Int.From_Word64 (I) + Math_Int.From_Word32 (1))) *
            Base ** (L + 1) mod
            Num_Of_Big_Int (M, M_First, L + 1) and
            (for all N in Natural range 0 .. 2 ** K - 1 =>
               (Num_Of_Big_Int (Aux4, Aux4_First + N * (L + 1), L + 1) =
                Num_Of_Big_Int (X, X_First, L + 1) ** (2 * N + 1) *
                Base ** (L + 1) mod
                Num_Of_Big_Int (M, M_First, L + 1))) and
            I < (Types.Word64 (E_Last - E_First) + 1) * 32);

         if Bit_Set (E, E_First, I) then
            W := 1;
            S := 0;
            J := 1;

            loop
               pragma Loop_Invariant
                 (L = A_Last - A_First and
                  Num_Of_Big_Int (Aux1, Aux1_First, L + 1) =
                  Math_Int.From_Word32 (1) and
                  Num_Of_Big_Int (Aux2, Aux2_First, L + 1) =
                  Num_Of_Big_Int (X, X_First, L + 1) *
                  Num_Of_Big_Int (X, X_First, L + 1) *
                  Base ** (L + 1) mod
                  Num_Of_Big_Int (M, M_First, L + 1) and
                  Num_Of_Big_Int (Aux3, Aux3_First, L + 1) =
                  Num_Of_Big_Int (X, X_First, L + 1) **
                  (Num_Of_Big_Int (E, E_First, E_Last - E_First + 1) /
                   Math_Int.From_Word32 (2) **
                     (Math_Int.From_Word64 (I) + Math_Int.From_Word32 (1))) *
                  Base ** (L + 1) mod
                  Num_Of_Big_Int (M, M_First, L + 1) and
                  (for all N in Natural range 0 .. 2 ** K - 1 =>
                     (Num_Of_Big_Int (Aux4, Aux4_First + N * (L + 1), L + 1) =
                      Num_Of_Big_Int (X, X_First, L + 1) ** (2 * N + 1) *
                      Base ** (L + 1) mod
                      Num_Of_Big_Int (M, M_First, L + 1))) and
                  Math_Int.From_Word32 (W) * Math_Int.From_Word32 (2) ** (J - S - 1) =
                  Num_Of_Big_Int (E, E_First, E_Last - E_First + 1) /
                  Math_Int.From_Word32 (2) ** (Math_Int.From_Word64 (I) -
                    (Math_Int.From_Integer (J) - Math_Int.From_Word32 (1))) mod
                  Math_Int.From_Word32 (2) ** J and
                  W mod 2 = 1 and 0 <= S and S < J and J <= K + 1 and
                  Math_Int.From_Integer (J) <=
                  Math_Int.From_Word64 (I) + Math_Int.From_Word32 (1) and
                  I < (Types.Word64 (E_Last - E_First) + 1) * 32);

               -- FIXME workaround for [N410-033]
               exit when not (J <= K and Types.Word64 (J) <= I);

               if Bit_Set (E, E_First, I - Types.Word64 (J)) then
                  W := Interfaces.Shift_Left (W, J - S) or 1;
                  S := J;
               end if;

               J := J + 1;
            end loop;

            S := S + 1;

            for H in Natural range 1 .. S
            loop
               pragma Loop_Invariant
                 (L = A_Last - A_First and
                  Num_Of_Big_Int (Aux1, Aux1_First, L + 1) =
                  Math_Int.From_Word32 (1) and
                  Num_Of_Big_Int (Aux2, Aux2_First, L + 1) =
                  Num_Of_Big_Int (X, X_First, L + 1) *
                  Num_Of_Big_Int (X, X_First, L + 1) *
                  Base ** (L + 1) mod
                  Num_Of_Big_Int (M, M_First, L + 1) and
                  Num_Of_Big_Int (Aux3, Aux3_First, L + 1) =
                  Num_Of_Big_Int (X, X_First, L + 1) **
                  (Num_Of_Big_Int (E, E_First, E_Last - E_First + 1) /
                   Math_Int.From_Word32 (2) **
                     (Math_Int.From_Word64 (I) + Math_Int.From_Word32 (1)) *
                   Math_Int.From_Word32 (2) ** (H - 1)) *
                  Base ** (L + 1) mod
                  Num_Of_Big_Int (M, M_First, L + 1) and
                  (for all N in Natural range 0 .. 2 ** K - 1 =>
                     (Num_Of_Big_Int (Aux4, Aux4_First + N * (L + 1), L + 1) =
                      Num_Of_Big_Int (X, X_First, L + 1) ** (2 * N + 1) *
                      Base ** (L + 1) mod
                      Num_Of_Big_Int (M, M_First, L + 1))) and
                  Math_Int.From_Word32 (W) =
                  Num_Of_Big_Int (E, E_First, E_Last - E_First + 1) /
                  Math_Int.From_Word32 (2) ** (Math_Int.From_Word64 (I) -
                    (Math_Int.From_Integer (S) - Math_Int.From_Word32 (1))) mod
                  Math_Int.From_Word32 (2) ** S and
                  W mod 2 = 1 and 0 <= S and S <= K + 1 and S'Loop_Entry = S and
                  Math_Int.From_Integer (S) <=
                  Math_Int.From_Word64 (I) + Math_Int.From_Word32 (1) and
                  I < (Types.Word64 (E_Last - E_First) + 1) * 32);

               Mont_Mult
                 (A, A_First, A_Last,
                  Aux3, Aux3_First, Aux3, Aux3_First,
                  M, M_First, M_Inv);

               Copy (A, A_First, A_Last, Aux3, Aux3_First);

               pragma Assert_And_Cut
                 (L = A_Last - A_First and
                  Num_Of_Big_Int (Aux1, Aux1_First, L + 1) =
                  Math_Int.From_Word32 (1) and
                  Num_Of_Big_Int (Aux2, Aux2_First, L + 1) =
                  Num_Of_Big_Int (X, X_First, L + 1) *
                  Num_Of_Big_Int (X, X_First, L + 1) *
                  Base ** (L + 1) mod
                  Num_Of_Big_Int (M, M_First, L + 1) and
                  Num_Of_Big_Int (Aux3, Aux3_First, L + 1) =
                  Num_Of_Big_Int (X, X_First, L + 1) **
                  (Num_Of_Big_Int (E, E_First, E_Last - E_First + 1) /
                   Math_Int.From_Word32 (2) **
                     (Math_Int.From_Word64 (I) + Math_Int.From_Word32 (1)) *
                   Math_Int.From_Word32 (2) ** H) *
                  Base ** (L + 1) mod
                  Num_Of_Big_Int (M, M_First, L + 1) and
                  (for all N in Natural range 0 .. 2 ** K - 1 =>
                     (Num_Of_Big_Int (Aux4, Aux4_First + N * (L + 1), L + 1) =
                      Num_Of_Big_Int (X, X_First, L + 1) ** (2 * N + 1) *
                      Base ** (L + 1) mod
                      Num_Of_Big_Int (M, M_First, L + 1))) and
                  Math_Int.From_Word32 (W) =
                  Num_Of_Big_Int (E, E_First, E_Last - E_First + 1) /
                  Math_Int.From_Word32 (2) ** (Math_Int.From_Word64 (I) -
                    (Math_Int.From_Integer (S) - Math_Int.From_Word32 (1))) mod
                  Math_Int.From_Word32 (2) ** S and
                  W mod 2 = 1 and 0 <= S and S <= K + 1 and S'Loop_Entry = S and
                  Math_Int.From_Integer (S) <=
                  Math_Int.From_Word64 (I) + Math_Int.From_Word32 (1) and
                  I < (Types.Word64 (E_Last - E_First) + 1) * 32);
            end loop;

            Mont_Mult
              (A, A_First, A_Last,
               Aux3, Aux3_First,
               Aux4, Aux4_First + Natural (Interfaces.Shift_Right (W, 1)) * (L + 1),
               M, M_First, M_Inv);

            Copy (A, A_First, A_Last, Aux3, Aux3_First);
         else
            S := 1;

            Mont_Mult
              (A, A_First, A_Last,
               Aux3, Aux3_First, Aux3, Aux3_First,
               M, M_First, M_Inv);

            Copy (A, A_First, A_Last, Aux3, Aux3_First);
         end if;

         pragma Assert_And_Cut
           (L = A_Last - A_First and
            Num_Of_Big_Int (Aux1, Aux1_First, L + 1) =
            Math_Int.From_Word32 (1) and
            Num_Of_Big_Int (Aux2, Aux2_First, L + 1) =
            Num_Of_Big_Int (X, X_First, L + 1) *
            Num_Of_Big_Int (X, X_First, L + 1) *
            Base ** (L + 1) mod
            Num_Of_Big_Int (M, M_First, L + 1) and
            Num_Of_Big_Int (Aux3, Aux3_First, L + 1) =
            Num_Of_Big_Int (X, X_First, L + 1) **
            (Num_Of_Big_Int (E, E_First, E_Last - E_First + 1) /
             Math_Int.From_Word32 (2) ** (Math_Int.From_Word64 (I) -
               Math_Int.From_Integer (S) + Math_Int.From_Word32 (1))) *
            Base ** (L + 1) mod
            Num_Of_Big_Int (M, M_First, L + 1) and
            (for all N in Natural range 0 .. 2 ** K - 1 =>
               (Num_Of_Big_Int (Aux4, Aux4_First + N * (L + 1), L + 1) =
                Num_Of_Big_Int (X, X_First, L + 1) ** (2 * N + 1) *
                Base ** (L + 1) mod
                Num_Of_Big_Int (M, M_First, L + 1))) and
            Math_Int.From_Integer (S) <=
            Math_Int.From_Word64 (I) + Math_Int.From_Word32 (1) and
            I < (Types.Word64 (E_Last - E_First) + 1) * 32);

         exit when I < Types.Word64 (S);

         I := I - Types.Word64 (S);
      end loop;

      Mont_Mult
        (A, A_First, A_Last,
         Aux3, Aux3_First, Aux1, Aux1_First,
         M, M_First, M_Inv);
   end Mont_Exp_Window;

end LSC.Bignum;
