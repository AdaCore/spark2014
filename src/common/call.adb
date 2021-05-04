------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                                 C A L L                                  --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2021, AdaCore                     --
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

with Ada.Directories;
with Ada.Direct_IO;
with Ada.Text_IO;
with GNATCOLL.Mmap;
with GNATCOLL.Utils;

package body Call is

   procedure Print_Command_Line
      (Command   : String;
       Arguments : Argument_List);
   --  Print the command line for debug purposes

   ------------------------
   -- Abort_With_Message --
   ------------------------

   procedure Abort_With_Message (Msg : String) is
   begin
      Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error, Msg);
      GNAT.OS_Lib.OS_Exit (1);
   end Abort_With_Message;

   ----------------------------------
   -- Argument_List_Of_String_List --
   ----------------------------------

   function Argument_List_Of_String_List (S : String_Lists.List)
      return Argument_List
   is
      use String_Lists;
      Arguments : Argument_List := (1 .. Integer (S.Length) => <>);
      Cnt       : Positive      := 1;
   begin
      for Elem of S loop
         Arguments (Cnt) := new String'(Elem);
         Cnt := Cnt + 1;
      end loop;
      return Arguments;
   end Argument_List_Of_String_List;

   ----------------------
   -- Call_With_Status --
   ----------------------

   procedure Call_With_Status
     (Command   : String;
      Arguments : String_Lists.List;
      Status    : out Integer;
      Output_FD : File_Descriptor := Standout;
      Verbose   : Boolean := False)
   is
      Executable : String_Access := Locate_Exec_On_Path (Command);
      Arg_List : Argument_List :=
        Argument_List_Of_String_List (Arguments);
   begin
      if Executable = null then
         Ada.Text_IO.Put_Line ("Could not find executable " & Command);
         GNAT.OS_Lib.OS_Exit (1);
      end if;

      if Verbose then
         Print_Command_Line (Command, Arg_List);
         Ada.Text_IO.New_Line;
      end if;

      Spawn (Executable.all, Arg_List, Output_FD, Status, Err_To_Out => True);
      GNATCOLL.Utils.Free (Arg_List);
      Free (Executable);
   end Call_With_Status;

   ------------------------
   -- Print_Command_Line --
   ------------------------

   procedure Print_Command_Line
      (Command   : String;
       Arguments : Argument_List)
   is
   begin
      Ada.Text_IO.Put (Command);

      for Arg of Arguments loop
         Ada.Text_IO.Put (" ");
         Ada.Text_IO.Put (Arg.all);
      end loop;
   end Print_Command_Line;

   -------------------------
   -- Read_File_Into_JSON --
   -------------------------

   function Read_File_Into_JSON (Fn : String) return JSON_Value
   is
      use GNATCOLL.Mmap;
      File   : Mapped_File;
      Region : Mapped_Region;

      Result : Read_Result;
   begin
      File := Open_Read (Fn);

      Read (File, Region);

      declare
         S : String (1 .. Integer (Length (File)));
         for S'Address use Data (Region).all'Address;
         --  A fake string directly mapped onto the file contents

      begin
         Result := Read (S);

         if not Result.Success then
            --  ??? We should close the file here, but the subprogram is likely
            --  to terminate anyway, so this is not crucial.
            raise Invalid_JSON_Stream with S;
         end if;
      end;

      Free (Region);
      Close (File);
      return Result.Value;
   end Read_File_Into_JSON;

   ---------------------------
   -- Read_File_Into_String --
   ---------------------------

   function Read_File_Into_String (Fn : String) return String
   is
      File_Size : constant Natural := Natural (Ada.Directories.Size (Fn));

      subtype File_String    is String (1 .. File_Size);
      package File_String_IO is new Ada.Direct_IO (File_String);

      File     : File_String_IO.File_Type;
      Contents : File_String;
   begin

      --  The read operation below will crash with an empty buffer

      if File_Size = 0 then
         return "";
      end if;

      File_String_IO.Open  (File, Mode => File_String_IO.In_File, Name => Fn);
      File_String_IO.Read  (File, Item => Contents);
      File_String_IO.Close (File);

      return Contents;
   end Read_File_Into_String;

end Call;
