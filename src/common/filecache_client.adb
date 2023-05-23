------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                      F I L E C A C H E _ C L I E N T                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2022-2023, AdaCore                     --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that  it will be useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General Public License  distributed with  gnatprove;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Directories; use Ada.Directories;
with Call;            use Call;

package body Filecache_Client is

   ----------
   -- Init --
   ----------

   function Init (Dir : String) return Filecache is
   begin
      return Filecache'(Dir => new String'(Dir));
   end Init;

   ---------
   -- Set --
   ---------

   procedure Set (Conn : Filecache; Key : String; Value : String) is
      Prev_Dir : constant String := Current_Directory;
      Fn       : constant String := Compose (Conn.Dir.all, Key);
      FD       : File_Descriptor;
      Name     : String_Access;
      Written  : Integer;
      Unused   : Boolean;
   begin
      --  We first write to a temporary file, then rename the file to the
      --  target filename. This should protect against:
      --    - Clients reading (via Get) the file while we write it, getting
      --      incomplete data. The file is always present with full data,
      --      or absent.
      --    - Two clients racing to write the file. Both clients would write to
      --      their own temporary file, and it doesn't matter which one "wins"
      --      the rename (renames last), as both should contain the same
      --      content.

      --  Renaming doesn't work across devices, so it's safer to create the
      --  temp file in the same directory. This is achieved by first switching
      --  directories.

      Set_Directory (Conn.Dir.all);

      Create_Temp_File (FD, Name);
      Written := Write (FD, Value (Value'First)'Address, Value'Length);
      Close (FD);
      if Written /= Value'Length then
         --  some error happened
         Delete_File (Name.all, Unused);
         goto Cleanup;
      end if;
      Rename_File (Name.all, Fn, Unused);

      << Cleanup >>
      Free (Name);
      Set_Directory (Prev_Dir);
   end Set;

   ---------
   -- Get --
   ---------

   function Get (Conn : Filecache; Key : String) return String is
      File : constant String := Compose (Conn.Dir.all, Key);
   begin
      if Exists (File) then
         return Read_File_Into_String (File);
      else
         return "";
      end if;
   end Get;

   -----------
   -- Close --
   -----------

   procedure Close (Conn : in out Filecache) is
   begin
      Free (Conn.Dir);
   end Close;

end Filecache_Client;
