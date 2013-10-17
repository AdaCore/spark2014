------------------------------------------------------------------------------
--                                                                          --
--                         GNAT COMPILER COMPONENTS                         --
--                                                                          --
--                             G E T _ T A R G                              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--          Copyright (C) 1992-2013, Free Software Foundation, Inc.         --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License --
-- for  more details.  You should have  received  a copy of the GNU General --
-- Public License  distributed with GNAT; see file COPYING3.  If not, go to --
-- http://www.gnu.org/licenses for a complete copy of the license.          --
--                                                                          --
-- GNAAMP, the GNAT Ada tool chain for the Rockwell Collins  AAMP family of --
-- microprocessors, is maintained by AdaCore (http://www.adacore.com).      --
--                                                                          --
------------------------------------------------------------------------------

--  This is the SPARK2014 specific body for this package

package body Get_Targ is

   -----------------------
   -- Get_Bits_Per_Unit --
   -----------------------

   function Get_Bits_Per_Unit return Pos is
   begin
      return 8;
   end Get_Bits_Per_Unit;

   -----------------------
   -- Get_Bits_Per_Word --
   -----------------------

   function Get_Bits_Per_Word return Pos is
   begin
      return 32;
   end Get_Bits_Per_Word;

   -------------------
   -- Get_Char_Size --
   -------------------

   function Get_Char_Size return Pos is
   begin
      return 8;
   end Get_Char_Size;

   -----------------
   -- Get_Wchar_T --
   -----------------

   function Get_Wchar_T_Size return Pos is
   begin
      return 16;
   end Get_Wchar_T_Size;

   --------------------
   -- Get_Short_Size --
   --------------------

   function Get_Short_Size return Pos is
   begin
      return 16;
   end Get_Short_Size;

   ------------------
   -- Get_Int_Size --
   ------------------

   function Get_Int_Size return Pos is
   begin
      return 32;
   end Get_Int_Size;

   -------------------
   -- Get_Long_Size --
   -------------------

   function Get_Long_Size return Pos is
   begin
      return 64;
   end Get_Long_Size;

   ------------------------
   -- Get_Long_Long_Size --
   ------------------------

   function Get_Long_Long_Size return Pos is
   begin
      return 64;
   end Get_Long_Long_Size;

   --------------------
   -- Get_Float_Size --
   --------------------

   function Get_Float_Size return Pos is
   begin
      return 32;
   end Get_Float_Size;

   ---------------------
   -- Get_Double_Size --
   ---------------------

   function Get_Double_Size return Pos is
   begin
      return 64;
   end Get_Double_Size;

   --------------------------
   -- Get_Long_Double_Size --
   --------------------------

   function Get_Long_Double_Size return Pos is
   begin
      return 96;
   end Get_Long_Double_Size;

   ----------------------
   -- Get_Pointer_Size --
   ----------------------

   function Get_Pointer_Size return Pos is
   begin
      return 64;
   end Get_Pointer_Size;

   ---------------------------
   -- Get_Maximum_Alignment --
   ---------------------------

   function Get_Maximum_Alignment return Pos is
   begin
      return 4;
   end Get_Maximum_Alignment;

   ------------------------------------
   -- Get_System_Allocator_Alignment --
   ------------------------------------

   function Get_System_Allocator_Alignment return Nat is
   begin
      return 1;
   end Get_System_Allocator_Alignment;

   ------------------------
   -- Get_Float_Words_BE --
   ------------------------

   function Get_Float_Words_BE return Nat is
   begin
      return 1;
   end Get_Float_Words_BE;

   ------------------
   -- Get_Words_BE --
   ------------------

   function Get_Words_BE return Nat is
   begin
      return 1;
   end Get_Words_BE;

   ------------------
   -- Get_Bytes_BE --
   ------------------

   function Get_Bytes_BE return Nat is
   begin
      return 1;
   end Get_Bytes_BE;

   -----------------
   -- Get_Bits_BE --
   -----------------

   function Get_Bits_BE return Nat is
   begin
      return 1;
   end Get_Bits_BE;

   ---------------------
   -- Get_Short_Enums --
   ---------------------

   function Get_Short_Enums return Int is
   begin
      return 0;
   end Get_Short_Enums;

   --------------------------
   -- Get_Strict_Alignment --
   --------------------------

   function Get_Strict_Alignment return Nat is
   begin
      return 1;
   end Get_Strict_Alignment;

   --------------------------------
   -- Get_Double_Float_Alignment --
   --------------------------------

   function Get_Double_Float_Alignment return Nat is
   begin
      return 0;
   end Get_Double_Float_Alignment;

   ---------------------------------
   -- Get_Double_Scalar_Alignment --
   ---------------------------------

   function Get_Double_Scalar_Alignment return Nat is
   begin
      return 0;
   end Get_Double_Scalar_Alignment;

   -----------------------------
   -- Get_Max_Unaligned_Field --
   -----------------------------

   function Get_Max_Unaligned_Field return Pos is
   begin
      return 64;  -- Can be different on some targets (e.g., AAMP)
   end Get_Max_Unaligned_Field;

   ----------------------
   -- Digits_From_Size --
   ----------------------

   function Digits_From_Size (Size : Pos) return Pos is
   begin
      if    Size =  32 then
         return  6;
      elsif Size =  48 then
         return  9;
      elsif Size =  64 then
         return 15;
      elsif Size =  96 then
         return 18;
      elsif Size = 128 then
         return 18;
      else
         raise Program_Error;
      end if;
   end Digits_From_Size;

   -----------------------------
   -- Register_Back_End_Types --
   -----------------------------

   procedure Register_Back_End_Types (Call_Back : Register_Type_Proc) is
      Float_Str  : C_String := (others => ASCII.NUL);
      Double_Str : C_String := (others => ASCII.NUL);

   begin
      Float_Str (Float_Str'First .. Float_Str'First + 4) := "float";
      Call_Back
        (C_Name => Float_Str, Digs => 6, Complex => False, Count  => 0,
         Float_Rep => IEEE_Binary, Size => 32, Alignment => 32);

      Double_Str (Double_Str'First .. Double_Str'First + 5) := "double";
      Call_Back
        (C_Name => Double_Str, Digs => 15, Complex => False, Count  => 0,
         Float_Rep => IEEE_Binary, Size => 64, Alignment => 64);
   end Register_Back_End_Types;

   ---------------------
   -- Width_From_Size --
   ---------------------

   function Width_From_Size  (Size : Pos) return Pos is
   begin
      if    Size =  8 then
         return  4;
      elsif Size = 16 then
         return  6;
      elsif Size = 32 then
         return 11;
      elsif Size = 64 then
         return 21;
      else
         raise Program_Error;
      end if;
   end Width_From_Size;

end Get_Targ;
