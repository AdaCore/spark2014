------------------------------------------------------------------------------
--                                                                          --
--                         GNAT COMPILER COMPONENTS                         --
--                                                                          --
--                             G E T _ T A R G                              --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 1998-2009, AdaCore                     --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 2,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License --
-- for  more details.  You should have  received  a copy of the GNU General --
-- Public License  distributed with GNAT;  see file COPYING.  If not, write --
-- to  the Free Software Foundation,  59 Temple Place - Suite 330,  Boston, --
-- MA 02111-1307, USA.                                                      --
--                                                                          --
------------------------------------------------------------------------------

--  This is the Hi-Lite version of package Get_Targ. This
--  package provides generic/dummy values related to types for Hi-Lite
--  backends.

with Types; use Types;

package Get_Targ is
   pragma Preelaborate;

   Get_Bits_Per_Unit           : Pos :=  8;
   Get_Bits_Per_Word           : Pos := 32;
   Get_Char_Size               : Pos :=  8;
   Get_Wchar_T_Size            : Pos := 16;
   Get_Short_Size              : Pos := 16;
   Get_Int_Size                : Pos := 32;
   Get_Long_Size               : Pos := 64;
   Get_Long_Long_Size          : Pos := 64;
   Get_Float_Size              : Pos := 32;
   Get_Double_Size             : Pos := 64;
   Get_Long_Double_Size        : Pos := 96;
   Get_Pointer_Size            : Pos := 32;
   Get_Maximum_Alignment       : Pos :=  4;
   Get_Float_Words_BE          : Nat :=  1;
   Get_Words_BE                : Nat :=  1;
   Get_Bytes_BE                : Nat :=  1;
   Get_Bits_BE                 : Nat :=  1;
   Get_Strict_Alignment        : Nat :=  1;
   Get_Double_Float_Alignment  : Nat :=  0;
   Get_Double_Scalar_Alignment : Nat :=  0;
   Get_Max_Priority            : Nat := 30;
   Get_Max_Interrupt_Priority  : Nat := 31;
   --  Do not use constants since these are functions in the default version,
   --  and GNAT may generate warnings about condition being always True.

   function Get_Max_Unaligned_Field return Pos;
   --  Returns the maximum supported size in bits for a field that is
   --  not aligned on a storage unit boundary.

   function Width_From_Size  (Size : Pos) return Pos;
   function Digits_From_Size (Size : Pos) return Pos;
   --  Calculate values for 'Width or 'Digits from 'Size

end Get_Targ;
