------------------------------------------------------------------------------
--                                                                          --
--                         GNAT BACK-END COMPONENTS                         --
--                                                                          --
--                           A L F A . C O M M O N                          --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--             Copyright (C) 2011, Free Software Foundation, Inc.           --
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
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

with Sdefault; use Sdefault;

package body ALFA.Common is

   function Is_From_Standard_Library (Loc : Source_Ptr) return Boolean is
   begin
      if Loc = Standard_Location then
         return False;
      else
         declare
            Dir_Name  : constant String := Include_Dir_Default_Name.all;
            File_Name : constant String :=
               Get_Name_String (Full_File_Name (Get_Source_File_Index (Loc)));
         begin
            return Dir_Name'Length <= File_Name'Length
              and then
                File_Name
                  (File_Name'First .. File_Name'First + Dir_Name'Length - 1)
                = Dir_Name;
         end;
      end if;
   end Is_From_Standard_Library;

end ALFA.Common;
