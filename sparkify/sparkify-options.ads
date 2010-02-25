------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                      S P A R K I F Y . O P T I O N S                     --
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

--  This package contains all the Sparkify options and control parameters, and
--  some auxiliary flags and objects needed to control special printing

with Hostparm;
with GNAT.OS_Lib; use GNAT.OS_Lib;

package Sparkify.Options is

   type Output_Modes is
   --  Defines the where and how sparkify places the result source
     (Pipe,
      --  Sends the output into Stderr
      Create_File,
      --  Creates the file with the name specified in 'o' option. If the
      --  file with the given name already exists, does not erase it and gives
      --  up
      Force_Create_File,
      --  Creates the file with the name specified in 'o' option. If the
      --  file with the given name already exists, erases the old file and
      --  replaces it with the pretty-printed source.
      Replace,
      --  Replaces the argument source with the pretty-printed source. The
      --  original source is stored in the file <arg_source>.npp
      --  (<arg_source>$NPP if on OpenVMS host). If the file with such a name
      --  already exists, sparkify gives up
      Force_Replace,
      --  Replaces the argument source with the pretty-printed source. The
      --  original source is stored in the file <arg_source>.npp
      --  (<arg_source>$NPP if on OpenVMS host). If the file with such a name
      --  already exists, sparkify overrides it
      Replace_No_Backup,
      --  Replaces the argument source with the pretty-printed source. The
      --  original source is not stored in any back-up file.
      Default);
      --  Put the result source into <arg_source>.pp (<arg_source>$PP if on
      --  OpenVMS host), overriding the existing file if any

   Output_Mode : Output_Modes := Default;

   type Output_Encodings is
   --  Defines the encodings used for the output file
     (Hex_ESC,
      Upper_Half,
      Shift_JIS,
      EUC,
      UTF_8,
      Brackets,
      Default);

   Output_Encoding : Output_Encodings := Default;
   --  Defines the encoding used for the result file(s).

   Form_String : String_Access := new String'("");
   --  Used as the value for the Form parameter of Open and Create procedures,
   --  defines the encoding of the result file

   ----------------------------------------------
   --  Options which are not set by parameters --
   ----------------------------------------------

   Max_Line_Length : constant Natural := Hostparm.Max_Line_Length;

end Sparkify.Options;
