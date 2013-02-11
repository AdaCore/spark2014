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

--  This is the Hi-Lite specific body for this package

package body Get_Targ is

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
   -- Get_Max_Unaligned_Field --
   -----------------------------

   function Get_Max_Unaligned_Field return Pos is
   begin
      return 64;  -- Can be different on some targets (e.g., AAMP)
   end Get_Max_Unaligned_Field;

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
