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

with LSC.Types;
with LSC.Math_Int;

use type LSC.Math_Int.Math_Int;
use type LSC.Types.Word32;
use type LSC.Types.Word64;

package LSC.Bignum
is

   function Base return Math_Int.Math_Int is (Math_Int.From_Word32 (2) ** 32)
     with Ghost;

   subtype Big_Int_Range is Natural range Natural'First .. Natural'Last - 1;

   type Big_Int is array (Big_Int_Range range <>) of Types.Word32;

   function Num_Of_Big_Int (A : Big_Int; F, L : Natural)
     return Math_Int.Math_Int
     with Ghost, Import, Global => null;

   function Num_Of_Boolean (B : Boolean) return Math_Int.Math_Int
     with Ghost, Import, Global => null;

   function Inverse (M, A : Math_Int.Math_Int) return Math_Int.Math_Int
     with Ghost, Import, Global => null;

   procedure Initialize
     (A       :    out Big_Int;
      A_First : in     Natural;
      A_Last  : in     Natural)
     with
       Depends =>
         (A => (A_First, A_Last)),
       Pre =>
         A_First in A'Range and
         A_Last in A'Range and
         A_First <= A_Last,
       Post =>
         (for all K in Natural range A_First .. A_Last => (A (K) = 0));

   procedure Copy
     (A       : in     Big_Int;
      A_First : in     Natural;
      A_Last  : in     Natural;
      B       : in out Big_Int;
      B_First : in     Natural)
     with
       Depends =>
         (B =>+ (A, A_First, A_Last, B_First)),
       Pre =>
         A_First in A'Range and
         A_Last in A'Range and
         A_First <= A_Last and
         B_First in B'Range and
         B_First + (A_Last - A_First) in B'Range,
       Post =>
         (for all K in Natural range B'Range =>
            ((if K in B_First .. B_First + A_Last - A_First then
                B (K) = A (A_First + K - B_First)) and
             (if K not in B_First .. B_First + A_Last - A_First then
                B (K) = B'Old (K))));

   procedure Sub_Inplace
     (A       : in out Big_Int;
      A_First : in     Natural;
      A_Last  : in     Natural;
      B       : in     Big_Int;
      B_First : in     Natural;
      Carry   :    out Boolean)
     with
       Depends =>
         ((A, Carry) => (A, A_First, A_Last, B, B_First)),
       Pre =>
         A_First in A'Range and
         A_Last in A'Range and
         B_First in B'Range and
         B_First + (A_Last - A_First) in B'Range and
         A_First <= A_Last,
       Post =>
         Num_Of_Big_Int (A'Old, A_First, A_Last - A_First + 1) -
         Num_Of_Big_Int (B, B_First, A_Last - A_First + 1) =
         Num_Of_Big_Int (A, A_First, A_Last - A_First + 1) -
         Base ** (A_Last - A_First + 1) * Num_Of_Boolean (Carry);

   function Less
     (A       : Big_Int;
      A_First : Natural;
      A_Last  : Natural;
      B       : Big_Int;
      B_First : Natural)
     return Boolean
     with
       Pre =>
         A_First in A'Range and
         A_Last in A'Range and
         B_First in B'Range and
         B_First + (A_Last - A_First) in B'Range and
         A_First <= A_Last,
       Post =>
         Less'Result =
         (Num_Of_Big_Int (A, A_First, A_Last - A_First + 1) <
          Num_Of_Big_Int (B, B_First, A_Last - A_First + 1));

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
     with
       Depends =>
         (A =>+ (A_First, A_Last, B, B_First, C, C_First, M, M_First, M_Inv)),
       Pre =>
         A_First in A'Range and then
         A_Last in A'Range and then
         A_First < A_Last and then
         B_First in B'Range and then
         B_First + (A_Last - A_First) in B'Range and then
         C_First in C'Range and then
         C_First + (A_Last - A_First) in C'Range and then
         M_First in M'Range and then
         M_First + (A_Last - A_First) in M'Range and then
         Num_Of_Big_Int (C, C_First, A_Last - A_First + 1) <
         Num_Of_Big_Int (M, M_First, A_Last - A_First + 1) and then
         Math_Int.From_Word32 (1) <
         Num_Of_Big_Int (M, M_First, A_Last - A_First + 1) and then
         1 + M_Inv * M (M_First) = 0,
       Post =>
         Num_Of_Big_Int (A, A_First, A_Last - A_First + 1) =
         (Num_Of_Big_Int (B, B_First, A_Last - A_First + 1) *
          Num_Of_Big_Int (C, C_First, A_Last - A_First + 1) *
          Inverse (Num_Of_Big_Int (M, M_First, A_Last - A_First + 1),
            Base) ** (A_Last - A_First + 1)) mod
         Num_Of_Big_Int (M, M_First, A_Last - A_First + 1);

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
     with
       Depends =>
         (A =>+
            (A_First, A_Last, X, X_First, E, E_First, E_Last,
             M, M_First, Aux1, Aux1_First, Aux2, Aux2_First,
             Aux3, Aux3_First, Aux4, Aux4_First,
             R, R_First, M_Inv, K),
          Aux1 =>
            (A_First, A_Last, Aux1_First),
          Aux2 =>+
            (A_First, A_Last, Aux2_First, Aux4, Aux4_First,
             X, X_First, R, R_First, M, M_First, M_Inv),
          Aux3 =>+
            (A, A_First, A_Last, X, X_First, E, E_First, E_Last,
             M, M_First, Aux1, Aux1_First, Aux2, Aux2_First, Aux3_First,
             Aux4, Aux4_First,
             R, R_First, M_Inv, K),
          Aux4 =>+
            (A, A_First, A_Last, X, X_First, Aux2, Aux2_First, Aux4_First,
             M, M_First, R, R_First, M_Inv, K)),
       Pre =>
         A_First in A'Range and then
         A_Last in A'Range and then
         A_First < A_Last and then
         X_First in X'Range and then
         X_First + (A_Last - A_First) in X'Range and then
         E_First in E'Range and then
         E_Last in E'Range and then
         E_First <= E_Last and then
         M_First in M'Range and then
         M_First + (A_Last - A_First) in M'Range and then
         Aux1_First in Aux1'Range and then
         Aux1_First + (A_Last - A_First) in Aux1'Range and then
         Aux2_First in Aux2'Range and then
         Aux2_First + (A_Last - A_First) in Aux2'Range and then
         Aux3_First in Aux3'Range and then
         Aux3_First + (A_Last - A_First) in Aux3'Range and then
         Aux4_First in Aux4'Range and then
         Aux4_First + (2 ** K * (A_Last - A_First + 1) - 1) in Aux4'Range and then
         K <= 30 and then
         R_First in R'Range and then
         R_First + (A_Last - A_First) in R'Range and then
         Num_Of_Big_Int (R, R_First, A_Last - A_First + 1) =
         Base ** (Math_Int.From_Integer (2) *
           Math_Int.From_Integer (A_Last - A_First + 1)) mod
         Num_Of_Big_Int (M, M_First, A_Last - A_First + 1) and then
         Math_Int.From_Word32 (1) <
         Num_Of_Big_Int (M, M_First, A_Last - A_First + 1) and then
         1 + M_Inv * M (M_First) = 0,
       Post =>
         Num_Of_Big_Int (A, A_First, A_Last - A_First + 1) =
         Num_Of_Big_Int (X, X_First, A_Last - A_First + 1) **
         Num_Of_Big_Int (E, E_First, E_Last - E_First + 1) mod
         Num_Of_Big_Int (M, M_First, A_Last - A_First + 1);

end LSC.Bignum;
