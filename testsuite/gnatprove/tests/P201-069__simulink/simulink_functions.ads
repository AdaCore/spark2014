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

--  Includes

--  with Ada.Numerics.Generic_Elementary_Functions;
with Ada.Numerics.Long_Elementary_Functions;
with Ada.Numerics.Elementary_Functions;
with Interfaces; use Interfaces;

package Simulink_Functions is

   package Long_Float_Numerics renames Ada.Numerics.Long_Elementary_Functions;
   package Float_Numerics renames Ada.Numerics.Elementary_Functions;

   --  Function prototypes

   function INT_And (Left, Right : Integer_8) return Integer_8;
   function INT_And (Left, Right : Integer_16) return Integer_16;
   function INT_And (Left, Right : Integer_32) return Integer_32;

   function INT_Or (Left, Right : Integer_8) return Integer_8;
   function INT_Or (Left, Right : Integer_16) return Integer_16;
   function INT_Or (Left, Right : Integer_32) return Integer_32;

   function INT_Xor (Left, Right : Integer_8) return Integer_8;
   function INT_Xor (Left, Right : Integer_16) return Integer_16;
   function INT_Xor (Left, Right : Integer_32) return Integer_32;

   function INT_Not (E : Integer_8) return Integer_8;
   function INT_Not (E : Integer_16) return Integer_16;
   function INT_Not (E : Integer_32) return Integer_32;

   function Exp_Fun (F : Float) return Float;
   function Exp_Fun (F : Long_Float) return Long_Float;

   function Log_Fun (F : Float) return Float;
   function Log_Fun (F : Long_Float) return Long_Float;

   function Log10_Fun (F : Float) return Float;
   function Log10_Fun (F : Long_Float) return Long_Float;

   function Mod_Fun_Sl (Left, Right : Integer_8) return Integer_8;
   function Mod_Fun_Sl (Left, Right : Integer_16) return Integer_16;
   function Mod_Fun_Sl (Left, Right : Integer_32) return Integer_32;

   function Mod_Fun_Sl (Left, Right : Unsigned_8) return Unsigned_8;
   function Mod_Fun_Sl (Left, Right : Unsigned_16) return Unsigned_16;
   function Mod_Fun_Sl (Left, Right : Unsigned_32) return Unsigned_32;

   function Mod_Fun_Sl (Left, Right : Float) return Float;
   function Mod_Fun_Sl (Left, Right : Long_Float) return Long_Float;

   function Mod_Fun (Left, Right : Integer_8) return Integer_8;
   function Mod_Fun (Left, Right : Integer_16) return Integer_16;
   function Mod_Fun (Left, Right : Integer_32) return Integer_32;

   function Mod_Fun (Left, Right : Unsigned_8) return Unsigned_8;
   function Mod_Fun (Left, Right : Unsigned_16) return Unsigned_16;
   function Mod_Fun (Left, Right : Unsigned_32) return Unsigned_32;

   function Mod_Fun (Left, Right : Integer) return Integer;
   function Mod_Fun (Left, Right : Float) return Float;
   function Mod_Fun (Left, Right : Long_Float) return Long_Float;

   function Rem_Fun (Left, Right : Integer_8) return Integer_8;
   function Rem_Fun (Left, Right : Integer_16) return Integer_16;
   function Rem_Fun (Left, Right : Integer_32) return Integer_32;

   function Rem_Fun (Left, Right : Unsigned_8) return Unsigned_8;
   function Rem_Fun (Left, Right : Unsigned_16) return Unsigned_16;
   function Rem_Fun (Left, Right : Unsigned_32) return Unsigned_32;

   function Rem_Fun (Left, Right : Float) return Float;
   function Rem_Fun (Left, Right : Long_Float) return Long_Float;

   function Sqrt_Fun (I : Unsigned_8) return Unsigned_8;
   function Sqrt_Fun (I : Unsigned_16) return Unsigned_16;
   function Sqrt_Fun (I : Unsigned_32) return Unsigned_32;

   function Sqrt_Fun (I : Integer_8) return Integer_8;
   function Sqrt_Fun (I : Integer_16) return Integer_16;
   function Sqrt_Fun (I : Integer_32) return Integer_32;

   function Sqrt_Fun (F : Float) return Float;
   function Sqrt_Fun (F : Long_Float) return Long_Float;

   function max (Left, Right : Unsigned_8) return Unsigned_8;
   function max (Left, Right : Unsigned_16) return Unsigned_16;
   function max (Left, Right : Unsigned_32) return Unsigned_32;

   function max (Left, Right : Integer_8) return Integer_8;
   function max (Left, Right : Integer_16) return Integer_16;
   function max (Left, Right : Integer_32) return Integer_32;

   function max (Left, Right : Float) return Float;
   function max (Left, Right : Long_Float) return Long_Float;

   function min (Left, Right : Unsigned_8) return Unsigned_8;
   function min (Left, Right : Unsigned_16) return Unsigned_16;
   function min (Left, Right : Unsigned_32) return Unsigned_32;

   function min (Left, Right : Integer_8) return Integer_8;
   function min (Left, Right : Integer_16) return Integer_16;
   function min (Left, Right : Integer_32) return Integer_32;

   function min (Left, Right : Float) return Float;
   function min (Left, Right : Long_Float) return Long_Float;

   function sign (I : Unsigned_8) return Unsigned_8;
   function sign (I : Unsigned_16) return Unsigned_16;
   function sign (I : Unsigned_32) return Unsigned_32;

   function sign (I : Integer_8) return Integer_8;
   function sign (I : Integer_16) return Integer_16;
   function sign (I : Integer_32) return Integer_32;

   function sign (F : Float) return Float;
   function sign (LF : Long_Float) return Long_Float;

   function cos (F : Float) return Float;
   function cos (LF : Long_Float) return Long_Float;

   function sin (F : Float) return Float;
   function sin (LF : Long_Float) return Long_Float;

   function tan (F : Float) return Float;
   function tan (LF : Long_Float) return Long_Float;

   function asin (F : Float) return Float;
   function asin (LF : Long_Float) return Long_Float;

   function acos (F : Float) return Float;
   function acos (LF : Long_Float) return Long_Float;

   function atan (F : Float) return Float;
   function atan (LF : Long_Float) return Long_Float;

   function sinh (F : Float) return Float;
   function sinh (LF : Long_Float) return Long_Float;

   function cosh (F : Float) return Float;
   function cosh (LF : Long_Float) return Long_Float;

   function tanh (F : Float) return Float;
   function tanh (LF : Long_Float) return Long_Float;

   function asinh (F : Float) return Float;
   function asinh (LF : Long_Float) return Long_Float;

   function acosh (F : Float) return Float;
   function acosh (LF : Long_Float) return Long_Float;

   function atanh (F : Float) return Float;
   function atanh (LF : Long_Float) return Long_Float;

   function atan2 (Left, Right : Float) return Float;
   function atan2 (Left, Right : Long_Float) return Long_Float;

   function Unsigned_8_To_Boolean (I : Unsigned_8) return Boolean;
   function Unsigned_16_To_Boolean (I : Unsigned_16) return Boolean;
   function Unsigned_32_To_Boolean (I : Unsigned_32) return Boolean;

   function Integer_8_To_Boolean (I : Integer_8) return Boolean;
   function Integer_16_To_Boolean (I : Integer_16) return Boolean;
   function Integer_32_To_Boolean (I : Integer_32) return Boolean;
   function Integer_To_Boolean (I : Integer) return Boolean;

   function Float_To_Boolean (R : Float) return Boolean;
   function Long_Float_To_Boolean (R : Long_Float) return Boolean;

   function Boolean_To_Unsigned_8 (B : Boolean) return Unsigned_8;
   function Boolean_To_Unsigned_16 (B : Boolean) return Unsigned_16;
   function Boolean_To_Unsigned_32 (B : Boolean) return Unsigned_32;

   function Boolean_To_Integer_8 (B : Boolean) return Integer_8;
   function Boolean_To_Integer_16 (B : Boolean) return Integer_16;
   function Boolean_To_Integer_32 (B : Boolean) return Integer_32;
   function Boolean_To_Integer (B : Boolean) return Integer;

   function Boolean_To_Float (B : Boolean) return Float;
   function Boolean_To_Long_Float (B : Boolean) return Long_Float;

   function pow (Left, Right : Float) return Float;
   function pow (Left, Right : Long_Float) return Long_Float;
   function pow (Left, Right : Integer_8) return Integer_8;
   function pow (Left, Right : Integer_16) return Integer_16;
   function pow (Left, Right : Integer_32) return Integer_32;

   function Ga_Shift_Left_U32 (Left, Right : Unsigned_32) return Unsigned_32;
   function Ga_Shift_Left_U16 (Left, Right : Unsigned_32) return Unsigned_16;
   function Ga_Shift_Left_U8 (Left, Right : Unsigned_32) return Unsigned_8;
   function Ga_Shift_Left_S32 (Left, Right : Unsigned_32) return Integer_32;
   function Ga_Shift_Left_S16 (Left, Right : Unsigned_32) return Integer_16;
   function Ga_Shift_Left_S8 (Left, Right : Unsigned_32) return Integer_8;

   function Ga_Shift_Right (Left, Right : Unsigned_8) return Unsigned_8;
   function Ga_Shift_Right (Left, Right : Unsigned_16) return Unsigned_16;
   function Ga_Shift_Right (Left, Right : Unsigned_32) return Unsigned_32;

end Simulink_Functions;
