------------------------------------------------------------------------------
--                             M O D E L I N G                              --
--                                                                          --
--                     Copyright (C) 2011-2015, AdaCore                     --
--                     Copyright (C) 2011-2015, IB Krates                   --
--                                                                          --
-- This library is free software;  you can redistribute it and/or modify it --
-- under terms of the  GNU General Public License  as published by the Free --
-- Software  Foundation;  either version 3,  or (at your  option) any later --
-- version. This library is distributed in the hope that it will be useful, --
-- but WITHOUT ANY WARRANTY;  without even the implied warranty of MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE.                            --
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
with Ada.Unchecked_Conversion;
with Ada.Numerics.Elementary_Functions;
with Ada.Numerics.Long_Elementary_Functions;

package body Simulink_Functions is

   --  signed to unsigned conversions

   function Int8ToU8 is new Ada.Unchecked_Conversion (Source => Integer_8,
                                                      Target => Unsigned_8);
   function Int16ToU16 is new Ada.Unchecked_Conversion (Source => Integer_16,
                                                        Target => Unsigned_16);
   function Int32ToU32 is new Ada.Unchecked_Conversion (Source => Integer_32,
                                                        Target => Unsigned_32);

   --  unsigned to signed conversions

   function U8ToInt8 is new Ada.Unchecked_Conversion (Source => Unsigned_8,
                                                      Target => Integer_8);
   function U16ToInt16 is new Ada.Unchecked_Conversion (Source => Unsigned_16,
                                                        Target => Integer_16);
   function U32ToInt32 is new Ada.Unchecked_Conversion (Source => Unsigned_32,
                                                        Target => Integer_32);

   function U32ToU16 is new Ada.Unchecked_Conversion (Source => Unsigned_32,
                                                        Target => Unsigned_16);
   function U32ToU8 is new Ada.Unchecked_Conversion (Source => Unsigned_32,
                                                        Target => Unsigned_8);
   function U32ToInt16 is new Ada.Unchecked_Conversion (Source => Unsigned_32,
                                                        Target => Integer_16);
   function U32ToInt8 is new Ada.Unchecked_Conversion (Source => Unsigned_32,
                                                        Target => Integer_8);

   -------------
   -- INT_And --
   -------------

   function INT_And (Left, Right : Integer_8) return Integer_8 is
   begin
      return U8ToInt8 (Int8ToU8 (Left) and Int8ToU8 (Right));
   end INT_And;

   -------------
   -- INT_And --
   -------------

   function INT_And (Left, Right : Integer_16) return Integer_16 is
   begin
      return U16ToInt16 (Int16ToU16 (Left) and Int16ToU16 (Right));
   end INT_And;

   -------------
   -- INT_And --
   -------------

   function INT_And (Left, Right : Integer_32) return Integer_32 is
   begin
      return U32ToInt32 (Int32ToU32 (Left) and Int32ToU32 (Right));
   end INT_And;

   ------------
   -- INT_Or --
   ------------

   function INT_Or (Left, Right : Integer_8) return Integer_8 is
   begin
      return U8ToInt8 (Int8ToU8 (Left) or Int8ToU8 (Right));
   end INT_Or;

   ------------
   -- INT_Or --
   ------------

   function INT_Or (Left, Right : Integer_16) return Integer_16 is
   begin
      return U16ToInt16 (Int16ToU16 (Left) or Int16ToU16 (Right));
   end INT_Or;

   ------------
   -- INT_Or --
   ------------

   function INT_Or (Left, Right : Integer_32) return Integer_32 is
   begin
      return U32ToInt32 (Int32ToU32 (Left) or Int32ToU32 (Right));
   end INT_Or;

   -------------
   -- INT_Xor --
   -------------

   function INT_Xor (Left, Right : Integer_8) return Integer_8 is
   begin
      return U8ToInt8 (Int8ToU8 (Left) xor Int8ToU8 (Right));
   end INT_Xor;

   -------------
   -- INT_Xor --
   -------------

   function INT_Xor (Left, Right : Integer_16) return Integer_16 is
   begin
      return U16ToInt16 (Int16ToU16 (Left) xor Int16ToU16 (Right));
   end INT_Xor;

   -------------
   -- INT_Xor --
   -------------

   function INT_Xor (Left, Right : Integer_32) return Integer_32 is
   begin
      return U32ToInt32 (Int32ToU32 (Left) xor Int32ToU32 (Right));
   end INT_Xor;

   -------------
   -- INT_Not --
   -------------

   function INT_Not (E : Integer_8) return Integer_8 is
   begin
      return U8ToInt8 (not Int8ToU8 (E));
   end INT_Not;

   -------------
   -- INT_Not --
   -------------

   function INT_Not (E : Integer_16) return Integer_16 is
   begin
      return U16ToInt16 (not Int16ToU16 (E));
   end INT_Not;

   -------------
   -- INT_Not --
   -------------

   function INT_Not (E : Integer_32) return Integer_32 is
   begin
      return U32ToInt32 (not Int32ToU32 (E));
   end INT_Not;

   ---------
   -- exp --
   ---------

   function Exp_Fun (F : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Exp (F);
   end Exp_Fun;

   ---------
   -- exp --
   ---------

   function Exp_Fun (F : Long_Float) return Long_Float is
   begin
      return Ada.Numerics.Long_Elementary_Functions.Exp (F);
   end Exp_Fun;

   ---------
   -- log --
   ---------

   function Log_Fun (F : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Log (F);
   end Log_Fun;

   ---------
   -- log --
   ---------

   function Log_Fun (F : Long_Float) return Long_Float is
      use Ada.Numerics.Long_Elementary_Functions;
   begin
      return Log (F);
   end Log_Fun;

   -----------
   -- log10 --
   -----------

   function Log10_Fun (F : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Log (X    => F,
                  Base => 10.0);
   end Log10_Fun;

   -----------
   -- log10 --
   -----------

   function Log10_Fun (F : Long_Float) return Long_Float is
      use Ada.Numerics.Long_Elementary_Functions;
   begin
      return Log (X    => F,
                  Base => 10.0);
   end Log10_Fun;

   ----------------
   -- Mod_Fun_Sl --
   ----------------

   function Mod_Fun_Sl (Left, Right : Integer_8) return Integer_8 is
   begin
      if Right = 0 then
         return Left;
      else
         if Left < 0 xor Right < 0 then
            declare
               Quotient : Integer_8 := abs (Left) / abs (Right);
            begin
               return Left - ((-1) * Quotient - 1) * Right;
            end;
         else
            return Left - (Left / Right) * Right;
         end if;
      end if;
   end Mod_Fun_Sl;

   ----------------
   -- Mod_Fun_Sl --
   ----------------

   function Mod_Fun_Sl (Left, Right : Integer_16) return Integer_16 is
   begin
      if Right = 0 then
         return Left;
      else
         if Left < 0 xor Right < 0 then
            declare
               Quotient : Integer_16 := abs (Left) / abs (Right);
            begin
               return Left - ((-1) * Quotient - 1) * Right;
            end;
         else
            return
              Left - (Left / Right) * Right;
         end if;
      end if;
   end Mod_Fun_Sl;

   ----------------
   -- Mod_Fun_Sl --
   ----------------

   function Mod_Fun_Sl (Left, Right : Integer_32) return Integer_32 is
   begin
      if Right = 0 then
         return Left;
      else
         if Left < 0 xor Right < 0 then
            declare
               Quotient : Integer_32 := abs (Left) / abs (Right);
            begin
               return Left - ((-1) * Quotient - 1) * Right;
            end;
         else
            return
              Left - (Left / Right) * Right;
         end if;
      end if;
   end Mod_Fun_Sl;

   ----------------
   -- Mod_Fun_Sl --
   ----------------

   function Mod_Fun_Sl (Left, Right : Unsigned_8) return Unsigned_8 is
   begin
      if Right = 0 then
         return Left;
      else
         return Left - (Left / Right) * Right;
      end if;
   end Mod_Fun_Sl;

   ----------------
   -- Mod_Fun_Sl --
   ----------------

   function Mod_Fun_Sl (Left, Right : Unsigned_16) return Unsigned_16 is
   begin
      if Right = 0 then
         return Left;
      else
         return Left - (Left / Right) * Right;
      end if;
   end Mod_Fun_Sl;

   ----------------
   -- Mod_Fun_Sl --
   ----------------

   function Mod_Fun_Sl (Left, Right : Unsigned_32) return Unsigned_32 is
   begin
      if Right = 0 then
         return Left;
      else
         return Left - (Left / Right) * Right;
      end if;
   end Mod_Fun_Sl;

   ----------------
   -- Mod_Fun_Sl --
   ----------------

   function Mod_Fun_Sl (Left, Right : Float) return Float is
   begin
      if Right = 0.0 then
         return Left;
      else
         return Left - Float'Floor (Left / Right) * Right;
      end if;
   end Mod_Fun_Sl;

   ----------------
   -- Mod_Fun_Sl --
   ----------------

   function Mod_Fun_Sl (Left, Right : Long_Float) return Long_Float is
   begin
      if Right = 0.0 then
         return Left;
      else
         return Left - Long_Float'Floor (Left / Right) * Right;
      end if;
   end Mod_Fun_Sl;

   -------------
   -- Mod_Fun --
   -------------

   function Mod_Fun (Left, Right : Integer_8) return Integer_8 is
   begin
      if Right = 0 then
         return Left;
      else
         return Left -
            Integer_8 (Float'Floor (Float (Left) / Float (Right))) * Right;
      end if;
   end Mod_Fun;

   -------------
   -- Mod_Fun --
   -------------

   function Mod_Fun (Left, Right : Integer_16) return Integer_16 is
   begin
      if Right = 0 then
         return Left;
      else
         return Left -
            Integer_16 (Float'Floor (Float (Left) / Float (Right))) * Right;
      end if;
   end Mod_Fun;

   -------------
   -- Mod_Fun --
   -------------

   function Mod_Fun (Left, Right : Integer_32) return Integer_32 is
   begin
      if Right = 0 then
         return Left;
      else
         return Left -
            Integer_32 (Float'Floor (Float (Left) / Float (Right))) * Right;
      end if;
   end Mod_Fun;

   -------------
   -- Mod_Fun --
   -------------

   function Mod_Fun (Left, Right : Unsigned_8) return Unsigned_8 is
   begin
      if Right = 0 then
         return Left;
      else
         return Left - (Left / Right) * Right;
      end if;
   end Mod_Fun;

   -------------
   -- Mod_Fun --
   -------------

   function Mod_Fun (Left, Right : Unsigned_16) return Unsigned_16 is
   begin
      if Right = 0 then
         return Left;
      else
         return Left - (Left / Right) * Right;
      end if;
   end Mod_Fun;

   -------------
   -- Mod_Fun --
   -------------

   function Mod_Fun (Left, Right : Unsigned_32) return Unsigned_32 is
   begin
      if Right = 0 then
         return Left;
      else
         return Left - (Left / Right) * Right;
      end if;
   end Mod_Fun;

   -------------
   -- Mod_Fun --
   -------------

   function Mod_Fun (Left, Right : Integer) return Integer is
   begin
      if Right = 0 then
         return Left;
      else
         return Left -
            Integer (Float'Floor (Float (Left) / Float (Right))) * Right;
      end if;
   end Mod_Fun;

   -------------
   -- Mod_Fun --
   -------------

   function Mod_Fun (Left, Right : Float) return Float is
   begin
      if Right = 0.0 then
         return Left;
      else
         return Left - Float'Floor (Left / Right) * Right;
      end if;
   end Mod_Fun;

   -------------
   -- Mod_Fun --
   -------------

   function Mod_Fun (Left, Right : Long_Float) return Long_Float is
   begin
      if Right = 0.0 then
         return Left;
      else
         return Left - Long_Float'Floor (Left / Right) * Right;
      end if;
   end Mod_Fun;

   -------------
   -- Rem_Fun --
   -------------

   function Rem_Fun (Left, Right : Integer_8) return Integer_8 is
   begin
      if Right = 0 then
         return 0;
      else
         return Left - (Left / Right) * Right;
      end if;
   end Rem_Fun;

   -------------
   -- Rem_Fun --
   -------------

   function Rem_Fun (Left, Right : Integer_16) return Integer_16 is
   begin
      if Right = 0 then
         return 0;
      else
         return Left - (Left / Right) * Right;
      end if;
   end Rem_Fun;

   -------------
   -- Rem_Fun --
   -------------

   function Rem_Fun (Left, Right : Integer_32) return Integer_32 is
   begin
      if Right = 0 then
         return 0;
      else
         return Left - (Left / Right) * Right;
      end if;
   end Rem_Fun;

   -------------
   -- Rem_Fun --
   -------------

   function Rem_Fun (Left, Right : Unsigned_8) return Unsigned_8 is
   begin
      if Right = 0 then
         return 0;
      else
         return Left - (Left / Right) * Right;
      end if;
   end Rem_Fun;

   -------------
   -- Rem_Fun --
   -------------

   function Rem_Fun (Left, Right : Unsigned_16) return Unsigned_16 is
   begin
      if Right = 0 then
         return 0;
      else
         return Left - (Left / Right) * Right;
      end if;
   end Rem_Fun;

   -------------
   -- Rem_Fun --
   -------------

   function Rem_Fun (Left, Right : Unsigned_32) return Unsigned_32 is
   begin
      if Right = 0 then
         return 0;
      else
         return Left - (Left / Right) * Right;
      end if;
   end Rem_Fun;

   -------------
   -- Rem_Fun --
   -------------

   function Rem_Fun (Left, Right : Float) return Float is
   begin
      return Left - Float'Truncation (Left / Right) * Right;
   end Rem_Fun;

   -------------
   -- Rem_Fun --
   -------------

   function Rem_Fun (Left, Right : Long_Float) return Long_Float is
   begin
      return Left - Long_Float'Truncation (Left / Right) * Right;
   end Rem_Fun;

   --------------
   -- Sqrt_Fun --
   --------------

   function Sqrt_Fun (I : Unsigned_8) return Unsigned_8 is
      use Ada.Numerics.Elementary_Functions;
   begin
      return Unsigned_8 (Sqrt (Float (I)));
   end Sqrt_Fun;

   --------------
   -- Sqrt_Fun --
   --------------

   function Sqrt_Fun (I : Unsigned_16) return Unsigned_16 is
      use Ada.Numerics.Elementary_Functions;
   begin
      return Unsigned_16 (Sqrt (Float (I)));
   end Sqrt_Fun;

   --------------
   -- Sqrt_Fun --
   --------------

   function Sqrt_Fun (I : Unsigned_32) return Unsigned_32 is
      use Ada.Numerics.Elementary_Functions;
   begin
      return Unsigned_32 (Sqrt (Float (I)));
   end Sqrt_Fun;

   --------------
   -- Sqrt_Fun --
   --------------

   function Sqrt_Fun (I : Integer_8) return Integer_8 is
      use Ada.Numerics.Elementary_Functions;
   begin
      return Integer_8 (Sqrt (Float (I)));
   end Sqrt_Fun;

   --------------
   -- Sqrt_Fun --
   --------------

   function Sqrt_Fun (I : Integer_16) return Integer_16 is
      use Ada.Numerics.Elementary_Functions;
   begin
      return Integer_16 (Sqrt (Float (I)));
   end Sqrt_Fun;

   --------------
   -- Sqrt_Fun --
   --------------

   function Sqrt_Fun (I : Integer_32) return Integer_32 is
      use Ada.Numerics.Elementary_Functions;
   begin
      return Integer_32 (Sqrt (Float (I)));
   end Sqrt_Fun;

   --------------
   -- Sqrt_Fun --
   --------------

   function Sqrt_Fun (F : Float) return Float is
      use Ada.Numerics.Long_Elementary_Functions;
   begin
      return Float (Sqrt (Long_Float (F)));
   end Sqrt_Fun;

   --------------
   -- Sqrt_Fun --
   --------------

   function Sqrt_Fun (F : Long_Float) return Long_Float is
      use Ada.Numerics.Long_Elementary_Functions;
   begin
      return Sqrt (F);
   end Sqrt_Fun;

   ---------
   -- max --
   ---------

   function max (Left, Right : Unsigned_8) return Unsigned_8 is
   begin
      if Left > Right then
         return Left;
      else
         return Right;
      end if;
   end max;

   ---------
   -- max --
   ---------

   function max (Left, Right : Unsigned_16) return Unsigned_16 is
   begin
      if Left > Right then
         return Left;
      else
         return Right;
      end if;
   end max;

   ---------
   -- max --
   ---------

   function max (Left, Right : Unsigned_32) return Unsigned_32 is
   begin
      if Left > Right then
         return Left;
      else
         return Right;
      end if;
   end max;

   ---------
   -- max --
   ---------

   function max (Left, Right : Integer_8) return Integer_8 is
   begin
      if Left > Right then
         return Left;
      else
         return Right;
      end if;
   end max;

   ---------
   -- max --
   ---------

   function max (Left, Right : Integer_16) return Integer_16 is
   begin
      if Left > Right then
         return Left;
      else
         return Right;
      end if;
   end max;

   ---------
   -- max --
   ---------

   function max (Left, Right : Integer_32) return Integer_32 is
   begin
      if Left > Right then
         return Left;
      else
         return Right;
      end if;
   end max;

   ---------
   -- max --
   ---------

   function max (Left, Right : Float) return Float is
   begin
      if Left > Right then
         return Left;
      else
         return Right;
      end if;
   end max;

   ---------
   -- max --
   ---------

   function max (Left, Right : Long_Float) return Long_Float is
   begin
      if Left > Right then
         return Left;
      else
         return Right;
      end if;
   end max;

   ---------
   -- min --
   ---------

   function min (Left, Right : Unsigned_8) return Unsigned_8 is
   begin
      if Left < Right then
         return Left;
      else
         return Right;
      end if;
   end min;

   ---------
   -- min --
   ---------

   function min (Left, Right : Unsigned_16) return Unsigned_16 is
   begin
      if Left < Right then
         return Left;
      else
         return Right;
      end if;
   end min;

   ---------
   -- min --
   ---------

   function min (Left, Right : Unsigned_32) return Unsigned_32 is
   begin
      if Left < Right then
         return Left;
      else
         return Right;
      end if;
   end min;

   ---------
   -- min --
   ---------

   function min (Left, Right : Integer_8) return Integer_8 is
   begin
      if Left < Right then
         return Left;
      else
         return Right;
      end if;
   end min;

   ---------
   -- min --
   ---------

   function min (Left, Right : Integer_16) return Integer_16 is
   begin
      if Left < Right then
         return Left;
      else
         return Right;
      end if;
   end min;

   ---------
   -- min --
   ---------

   function min (Left, Right : Integer_32) return Integer_32 is
   begin
      if Left < Right then
         return Left;
      else
         return Right;
      end if;
   end min;

   ---------
   -- min --
   ---------

   function min (Left, Right : Float) return Float is
   begin
      if Left < Right then
         return Left;
      else
         return Right;
      end if;
   end min;

   ---------
   -- min --
   ---------

   function min (Left, Right : Long_Float) return Long_Float is
   begin
      if Left < Right then
         return Left;
      else
         return Right;
      end if;
   end min;

   ----------
   -- sign --
   ----------

   function sign (I : Unsigned_8) return Unsigned_8 is
   begin
      if I = 0 then
         return 0;
      else
         return 1;
      end if;
   end sign;

   ----------
   -- sign --
   ----------

   function sign (I : Unsigned_16) return Unsigned_16 is
   begin
      if I = 0 then
         return 0;
      else
         return 1;
      end if;
   end sign;

   ----------
   -- sign --
   ----------

   function sign (I : Unsigned_32) return Unsigned_32 is
   begin
      if I = 0 then
         return 0;
      else
         return 1;
      end if;
   end sign;

   ----------
   -- sign --
   ----------

   function sign (I : Integer_8) return Integer_8 is
   begin
      if I = 0 then
         return 0;
      elsif I > 0 then
         return 1;
      else
         return -1;
      end if;
   end sign;

   ----------
   -- sign --
   ----------

   function sign (I : Integer_16) return Integer_16 is
   begin
      if I = 0 then
         return 0;
      elsif I > 0 then
         return 1;
      else
         return -1;
      end if;
   end sign;

   ----------
   -- sign --
   ----------

   function sign (I : Integer_32) return Integer_32 is
   begin
      if I = 0 then
         return 0;
      elsif I > 0 then
         return 1;
      else
         return -1;
      end if;
   end sign;

   ----------
   -- sign --
   ----------

   function sign (F : Float) return Float is
   begin
      if F = 0.0 then
         return 0.0;
      elsif F > 0.0 then
         return 1.0;
      else
         return -1.0;
      end if;
   end sign;

   ----------
   -- sign --
   ----------

   function sign (LF : Long_Float) return Long_Float is
   begin
      if LF = 0.0 then
         return 0.0;
      elsif LF > 0.0 then
         return 1.0;
      else
         return -1.0;
      end if;
   end sign;

   ---------
   -- cos --
   ---------

   function cos (F : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Cos (F);
   end cos;

   ---------
   -- cos --
   ---------

   function cos (LF : Long_Float) return Long_Float is
   begin
      return Ada.Numerics.Long_Elementary_Functions.Cos (LF);
   end cos;

   ---------
   -- sin --
   ---------

   function sin (F : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Sin (F);
   end sin;

   ---------
   -- sin --
   ---------

   function sin (LF : Long_Float) return Long_Float is
   begin
      return Ada.Numerics.Long_Elementary_Functions.Sin (LF);
   end sin;

   ---------
   -- tan --
   ---------

   function tan (F : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Tan (F);
   end tan;

   ---------
   -- tan --
   ---------

   function tan (LF : Long_Float) return Long_Float is
   begin
      return Ada.Numerics.Long_Elementary_Functions.Tan (LF);
   end tan;

   ----------
   -- asin --
   ----------

   function asin (F : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Arcsin (F);
   end asin;

   ----------
   -- asin --
   ----------

   function asin (LF : Long_Float) return Long_Float is
   begin
      return Ada.Numerics.Long_Elementary_Functions.Arcsin (LF);
   end asin;

   ----------
   -- acos --
   ----------

   function acos (F : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Arccos (F);
   end acos;

   ----------
   -- acos --
   ----------

   function acos (LF : Long_Float) return Long_Float is
   begin
      return Ada.Numerics.Long_Elementary_Functions.Arccos (LF);
   end acos;

   ----------
   -- atan --
   ----------

   function atan (F : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Arctan (F);
   end atan;

   ----------
   -- atan --
   ----------

   function atan (LF : Long_Float) return Long_Float is
   begin
      return Ada.Numerics.Long_Elementary_Functions.Arctan (LF);
   end atan;

   ----------
   -- sinh --
   ----------

   function sinh (F : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Sinh (F);
   end sinh;

   ----------
   -- sinh --
   ----------

   function sinh (LF : Long_Float) return Long_Float is
   begin
      return Ada.Numerics.Long_Elementary_Functions.Sinh (LF);
   end sinh;

   ----------
   -- cosh --
   ----------

   function cosh (F : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Cosh (F);
   end cosh;

   ----------
   -- cosh --
   ----------

   function cosh (LF : Long_Float) return Long_Float is
   begin
      return Ada.Numerics.Long_Elementary_Functions.Cosh (LF);
   end cosh;

   ----------
   -- tanh --
   ----------

   function tanh (F : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Tanh (F);
   end tanh;

   ----------
   -- tanh --
   ----------

   function tanh (LF : Long_Float) return Long_Float is
   begin
      return Ada.Numerics.Long_Elementary_Functions.Tanh (LF);
   end tanh;

   -----------
   -- asinh --
   -----------

   function asinh (F : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Arcsinh (F);
   end asinh;

   -----------
   -- asinh --
   -----------

   function asinh (LF : Long_Float) return Long_Float is
   begin
      return Ada.Numerics.Long_Elementary_Functions.Arcsinh (LF);
   end asinh;

   -----------
   -- acosh --
   -----------

   function acosh (F : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Arccosh (F);
   end acosh;

   -----------
   -- acosh --
   -----------

   function acosh (LF : Long_Float) return Long_Float is
   begin
      return Ada.Numerics.Long_Elementary_Functions.Arccosh (LF);
   end acosh;

   -----------
   -- atanh --
   -----------

   function atanh (F : Float) return Float is
   begin
      return Ada.Numerics.Elementary_Functions.Arctanh (F);
   end atanh;

   -----------
   -- atanh --
   -----------

   function atanh (LF : Long_Float) return Long_Float is
   begin
      return Ada.Numerics.Long_Elementary_Functions.Arctanh (LF);
   end atanh;

   -----------
   -- atan2 --
   -----------

   function atan2 (Left : Float; Right : Float) return Float is
   begin
      return Float (atan2 (Long_Float (Left), Long_Float (Right)));
   end atan2;

   -----------
   -- atan2 --
   -----------

   function atan2 (Left : Long_Float; Right : Long_Float) return Long_Float is
      Result      : Long_Float;
      Pi          : constant Long_Float := 3.14159265358979323846;
      Pi_Over_Two : constant Long_Float := 1.57079632679489661923;
   begin
      if (Left = 0.0) and then (Right = 0.0) then
         return 0.0;
      elsif abs (Left) <= abs (Right) then
         Result := atan (Left / Right);
         if Right <= 0.0 then
            if Left <= 0.0 then
               Result := Result - Pi;
            else
               Result := Result + Pi;
            end if;
         end if;
         return Result;
      else
         Result := atan (-Right / Left);
         if Left <= 0.0 then
            Result := Result - Pi_Over_Two;
         else
            Result := Result + Pi_Over_Two;
         end if;
         return Result;
      end if;
   end atan2;

   --  boolean conversions

   ---------------------------
   -- Unsigned_8_To_Boolean --
   ---------------------------

   function Unsigned_8_To_Boolean (I : Unsigned_8) return Boolean
   is
   begin
      return I /= 0;
   end Unsigned_8_To_Boolean;

   ----------------------------
   -- Unsigned_16_To_Boolean --
   ----------------------------

   function Unsigned_16_To_Boolean (I : Unsigned_16) return Boolean
   is
   begin
      return I /= 0;
   end Unsigned_16_To_Boolean;

   ----------------------------
   -- Unsigned_32_To_Boolean --
   ----------------------------

   function Unsigned_32_To_Boolean (I : Unsigned_32) return Boolean
   is
   begin
      return I /= 0;
   end Unsigned_32_To_Boolean;

   --------------------------
   -- Integer_8_To_Boolean --
   --------------------------

   function Integer_8_To_Boolean (I : Integer_8) return Boolean
   is
   begin
      return I /= 0;
   end Integer_8_To_Boolean;

   ---------------------------
   -- Integer_16_To_Boolean --
   ---------------------------

   function Integer_16_To_Boolean (I : Integer_16) return Boolean
   is
   begin
      return I /= 0;
   end Integer_16_To_Boolean;

   ---------------------------
   -- Integer_32_To_Boolean --
   ---------------------------

   function Integer_32_To_Boolean (I : Integer_32) return Boolean
   is
   begin
      return I /= 0;
   end Integer_32_To_Boolean;

   ------------------------
   -- Integer_To_Boolean --
   ------------------------

   function Integer_To_Boolean (I : Integer) return Boolean
   is
   begin
      return I /= 0;
   end Integer_To_Boolean;

   -----------------------
   -- Float_To_Boolean --
   -----------------------

   function Float_To_Boolean (R : Float) return Boolean
   is
   begin
      return Long_Float (R) /= 0.0;
   end Float_To_Boolean;

   ---------------------------
   -- Long_Float_To_Boolean --
   ---------------------------

   function Long_Float_To_Boolean (R : Long_Float) return Boolean
   is
   begin
      return R /= 0.0;
   end Long_Float_To_Boolean;

   ---------------------------
   -- Boolean_To_Unsigned_8 --
   ---------------------------

   function Boolean_To_Unsigned_8 (B : Boolean) return Unsigned_8
   is
      Res : Unsigned_8;
   begin
      if not B then
         Res := 0;
      else
         Res := 1;
      end if;
      return Res;
   end Boolean_To_Unsigned_8;

   ----------------------------
   -- Boolean_To_Unsigned_16 --
   ----------------------------

   function Boolean_To_Unsigned_16 (B : Boolean) return Unsigned_16
   is
      Res : Unsigned_16;
   begin
      if not B then
         Res := 0;
      else
         Res := 1;
      end if;
      return Res;
   end Boolean_To_Unsigned_16;

   ----------------------------
   -- Boolean_To_Unsigned_32 --
   ----------------------------

   function Boolean_To_Unsigned_32 (B : Boolean) return Unsigned_32
   is
      Res : Unsigned_32;
   begin
      if not B then
         Res := 0;
      else
         Res := 1;
      end if;
      return Res;
   end Boolean_To_Unsigned_32;

   --------------------------
   -- Boolean_To_Integer_8 --
   --------------------------

   function Boolean_To_Integer_8 (B : Boolean) return Integer_8
   is
      Res : Integer_8;
   begin
      if not B then
         Res := 0;
      else
         Res := 1;
      end if;
      return Res;
   end Boolean_To_Integer_8;

   ---------------------------
   -- Boolean_To_Integer_16 --
   ---------------------------

   function Boolean_To_Integer_16 (B : Boolean) return Integer_16
   is
      Res : Integer_16;
   begin
      if not B then
         Res := 0;
      else
         Res := 1;
      end if;
      return Res;
   end Boolean_To_Integer_16;

   ----------------------------
   -- Boolean_To_Integer_32 --
   ----------------------------

   function Boolean_To_Integer_32 (B : Boolean) return Integer_32
   is
      Res : Integer_32;
   begin
      if not B then
         Res := 0;
      else
         Res := 1;
      end if;
      return Res;
   end Boolean_To_Integer_32;

   ------------------------
   -- Boolean_To_Integer --
   ------------------------

   function Boolean_To_Integer (B : Boolean) return Integer
   is
      Res : Integer;
   begin
      if not B then
         Res := 0;
      else
         Res := 1;
      end if;
      return Res;
   end Boolean_To_Integer;

   ----------------------
   -- Boolean_To_Float --
   ----------------------

   function Boolean_To_Float (B : Boolean) return Float
   is
      Res : Float;
   begin
      if not B then
         Res := 0.0;
      else
         Res := 1.0;
      end if;
      return Res;
   end Boolean_To_Float;

   ---------------------------
   -- Boolean_To_Long_Float --
   ---------------------------

   function Boolean_To_Long_Float (B : Boolean) return Long_Float
   is
      Res : Long_Float;
   begin
      if not B then
         Res := 0.0;
      else
         Res := 1.0;
      end if;
      return Res;
   end Boolean_To_Long_Float;

   ---------
   -- pow --
   ---------

   function pow (Left, Right : Float) return Float
   is
      use Float_Numerics;
   begin
      return Left ** Right;
   end pow;

   ---------
   -- pow --
   ---------

   function pow (Left, Right : Long_Float) return Long_Float
   is
      use Long_Float_Numerics;
   begin
      return Left ** Right;
   end pow;

   ---------
   -- pow --
   ---------

   function pow (Left, Right : Integer_8) return Integer_8
   is
   begin
      return Left ** Natural (Right);
   end pow;

   ---------
   -- pow --
   ---------

   function pow (Left, Right : Integer_16) return Integer_16
   is
   begin
      return Left ** Natural (Right);
   end pow;

   ---------
   -- pow --
   ---------

   function pow (Left, Right : Integer_32) return Integer_32
   is
   begin
      return Left ** Natural (Right);
   end pow;

   ----------------
   -- Shift_Left --
   ----------------

   function Ga_Shift_Left_U32 (Left, Right : Unsigned_32) return Unsigned_32 is
   begin
      return Shift_Left (Left, Natural (Right) mod 32);
   end Ga_Shift_Left_U32;

   ----------------
   -- Shift_Left --
   ----------------

   function Ga_Shift_Left_U16 (Left, Right : Unsigned_32) return Unsigned_16 is
   begin
      return U32ToU16 (Shift_Left (Left, Natural (Right) mod 32));
   end Ga_Shift_Left_U16;

   ----------------
   -- Shift_Left --
   ----------------

   function Ga_Shift_Left_U8 (Left, Right : Unsigned_32) return Unsigned_8 is
   begin
      return U32ToU8 (Shift_Left (Left, Natural (Right) mod 32));
   end Ga_Shift_Left_U8;

   ----------------
   -- Shift_Left --
   ----------------

   function Ga_Shift_Left_S32 (Left, Right : Unsigned_32) return Integer_32 is
   begin
      return U32ToInt32 (Shift_Left (Left, Natural (Right) mod 32));
   end Ga_Shift_Left_S32;

   ----------------
   -- Shift_Left --
   ----------------

   function Ga_Shift_Left_S16 (Left, Right : Unsigned_32) return Integer_16 is
   begin
      return U32ToInt16 (Shift_Left (Left, Natural (Right) mod 32));
   end Ga_Shift_Left_S16;

   ----------------
   -- Shift_Left --
   ----------------

   function Ga_Shift_Left_S8 (Left, Right : Unsigned_32) return Integer_8 is
   begin
      return U32ToInt8 (Shift_Left (Left, Natural (Right) mod 32));
   end Ga_Shift_Left_S8;

   -----------------
   -- Shift_Right --
   -----------------

   function Ga_Shift_Right (Left, Right : Unsigned_8) return Unsigned_8 is
   begin
      return Shift_Right (Left, Natural (Right) mod 32);
   end Ga_Shift_Right;

   -----------------
   -- Shift_Right --
   -----------------

   function Ga_Shift_Right (Left, Right : Unsigned_16) return Unsigned_16 is
   begin
      return Shift_Right (Left, Natural (Right) mod 32);
   end Ga_Shift_Right;

   -----------------
   -- Shift_Right --
   -----------------

   function Ga_Shift_Right (Left, Right : Unsigned_32) return Unsigned_32 is
   begin
      return Shift_Right (Left, Natural (Right) mod 32);
   end Ga_Shift_Right;

end Simulink_Functions;
