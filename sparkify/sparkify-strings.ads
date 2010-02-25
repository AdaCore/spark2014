------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                      S P A R K I F Y . S T R I N G S                     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                     Copyright (C) 2009-2010, AdaCore                     --
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

--  This package provides the efficient string storage mechanism for varied
--  length strings

package Sparkify.Strings is

   type String_Loc is record
      First, Last : Natural;
   end record;
   --  This record contains the start and end positions of a string inside
   --  a character table

   Nil_String_Loc : String_Loc := (0, 0);
   --  Corresponds to an empty string

   function Enter_String (S : String) return String_Loc;
   --  Stores a string in a character array, returning its starting and ending
   --  positions in a String_Loc structure

   function Get_String (SL : String_Loc) return String;
   --  Retrieves a string from a character array, based on its starting
   --  and ending positions supplied by SL

   procedure Init;
   --  Resets the string table

end Sparkify.Strings;
