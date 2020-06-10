------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                U T I L S                                 --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

package body Utils is

   ------------------
   -- Strip_Prefix --
   ------------------

   function Strip_Prefix (Name : String) return String is
      Start : Integer := Name'First;
   begin
      for J in Name'Range loop
         if Name (J) = '_' then
            Start := J + 1;
            exit;
         end if;
      end loop;

      return Name (Start .. Name'Last);
   end Strip_Prefix;

   ------------------
   -- Strip_Suffix --
   ------------------

   function Strip_Suffix (Name : String) return String is
      Stop : Integer := Name'Last;
   begin
      for J in reverse Name'Range loop
         if Name (J) = '_' then
            Stop := J - 1;
            exit;
         end if;
      end loop;

      return Name (Name'First .. Stop);
   end Strip_Suffix;

   ------------
   -- Suffix --
   ------------

   function Suffix (Name : String) return String is
      Stop : Integer := Name'Last;
   begin
      for J in reverse Name'Range loop
         if Name (J) = '_' then
            Stop := J;
            exit;
         end if;
      end loop;

      return Name (Stop + 1 .. Name'Last);
   end Suffix;

end Utils;
