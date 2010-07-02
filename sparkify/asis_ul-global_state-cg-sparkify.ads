------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--     A S I S _ U L . G L O B A L _ S T A T E . C G . S P A R K I F Y      --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
--                                                                          --
-- Sparkify is  free  software;  you can redistribute it  and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. Sparkify is distributed in the hope that it will be useful, but --
-- WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHANTABI- --
-- LITY or  FITNESS  FOR A  PARTICULAR  PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- Sparkify is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

--  This package defines sparkify-specific call graph routines

with Ada.Strings.Wide_Unbounded;       use Ada.Strings.Wide_Unbounded;

with Sparkify.Stringset;               use Sparkify;

package ASIS_UL.Global_State.CG.Sparkify is

   procedure Global_Effects
     (El              : Asis.Element;
      Sep             : Wide_String;
      Reads_Str       : out Unbounded_Wide_String;
      Writes_Str      : out Unbounded_Wide_String;
      Read_Writes_Str : out Unbounded_Wide_String);

   function Global_Reads
     (El  : Asis.Element;
      Sep : Wide_String) return Unbounded_Wide_String;

   function All_Global_Reads
     (El  : Asis.Element;
      Sep : Wide_String) return Unbounded_Wide_String;

   function Global_Writes
     (El  : Asis.Element;
      Sep : Wide_String) return Unbounded_Wide_String;

   function All_Global_Writes
     (El  : Asis.Element;
      Sep : Wide_String;
      Set : Stringset.Set) return Unbounded_Wide_String;

   function Global_Read_Writes
     (El  : Asis.Element;
      Sep : Wide_String) return Unbounded_Wide_String;

end ASIS_UL.Global_State.CG.Sparkify;
