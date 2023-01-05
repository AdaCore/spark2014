------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--              S P A R K _ M E M C A C H E D _ W R A P P E R               --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2017-2022, AdaCore                     --
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

with Ada.Command_Line; use Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Strings.Fixed;
with Ada.Text_IO;
with Cache_Client;
with Filecache_Client;
with GNAT.Expect;      use GNAT.Expect;
with GNAT.OS_Lib;      use GNAT.OS_Lib;
with GNAT.SHA1;
with GNAT.Sockets;     use GNAT.Sockets;
with GNATCOLL.JSON;    use GNATCOLL.JSON;
with GNATCOLL.Mmap;
with Memcache_Client;

procedure SPARK_Memcached_Wrapper
  with No_Return
is

   --  This is a wrapper program, which caches identical invocations of
   --  gnatwhy3 and provers by hashing the input to the tool (commandline and
   --  input files), and compares this hash with previous runs of the same
   --  tool. If a match is found, the output of the previous run is output.

   --  Invocation:
   --  spark_memcached_wrapper salt hostname:port commandname <args> filename

   --  The salt is an arbitrary string that is hashed as well, but is not part
   --  of the command name or command line of the tool.

   procedure Hash_Commandline (C : in out GNAT.SHA1.Context);
   --  @param C the hash context to be updated
   --  Compute a hash of the commandline provided to the wrapper. The procedure
   --  starts hashing at the second argument (the command name) and stops
   --  before the last (the file name). This procedure only has special
   --  handling for arguments of gnatwhy3 currently. This means that some
   --  arguments which can be ignored are skipped, for others, instead of
   --  the argument some other content is hashed.

   procedure Hash_Binary (C : in out GNAT.SHA1.Context; Execname : String);
   --  If the binary Fn is on the PATH and there is a file Fn.hash next to it,
   --  we read that file and add it to the context.

   procedure Hash_File (C : in out GNAT.SHA1.Context; Fn : String);
   --  @param C the hash context to be updated
   --  @param Fn the file to be hashed
   --  Compute a hash of the file in argument

   function Compute_Key return GNAT.SHA1.Message_Digest;
   --  @return the key to be used for this invocation of the wrapper in the
   --    memcached table

   function Init_Client return Cache_Client.Cache'Class;
   --  @return a connection to the memcached server specified by the first
   --    command line argument

   procedure Report_Error (Msg : String)
     with No_Return;
   --  @param Msg error message to be reported
   --  Quit the program and transmit a message in gnatwhy3 style

   -----------------
   -- Hash_Binary --
   -----------------

   procedure Hash_Binary (C : in out GNAT.SHA1.Context; Execname : String)
   is

      function Compute_Hash_Filename (Exec : String) return String;
      --  Compute the hashfile name from the executable name by locating the
      --  file in the PATH, then adding ".hash", or replacing the suffix with
      --  ".hash", if any.

      ---------------------------
      -- Compute_Hash_Filename --
      ---------------------------

      function Compute_Hash_Filename (Exec : String) return String is
         Fn : String_Access := GNAT.OS_Lib.Locate_Exec_On_Path (Exec);
      begin
         if Fn = null then
            return "";
         end if;
         declare
            Ext : constant String := Ada.Directories.Extension (Fn.all);
         begin
            return Result : constant String :=
              (if Ext = "" then Fn.all & ".hash"
               else Fn (Fn'First .. Fn'Last - Ext'Length) & ".hash") do
               Free (Fn);
            end return;
         end;
      end Compute_Hash_Filename;

      Hash_Fn : constant String := Compute_Hash_Filename (Execname);
   begin
      if Hash_Fn /= "" and then Ada.Directories.Exists (Hash_Fn) then
         Hash_File (C, Hash_Fn);
      end if;
   end Hash_Binary;

   ----------------------
   -- Hash_Commandline --
   ----------------------

   procedure Hash_Commandline (C : in out GNAT.SHA1.Context) is
      I : Positive := 3;
   begin
      while I < Ada.Command_Line.Argument_Count loop
         declare
            Arg : constant String := Ada.Command_Line.Argument (I);
         begin
            if Arg = "-j" or else Arg = "--socket" then
               I := I + 2;
            elsif Arg = "--debug"
              or else Arg = "--force"
              or else Arg = "-f"
            then
               I := I + 1;
            elsif Arg = "--why3-conf" then
               Hash_File (C, Ada.Command_Line.Argument (I + 1));
               I := I + 2;
            else
               GNAT.SHA1.Update (C, Arg);
               I := I + 1;
            end if;
         end;
      end loop;
   end Hash_Commandline;

   ---------------
   -- Hash_File --
   ---------------

   procedure Hash_File (C : in out GNAT.SHA1.Context; Fn : String) is
      use GNATCOLL.Mmap;
      File   : Mapped_File;
      Region : Mapped_Region;

   begin
      File := Open_Read (Fn);

      Read (File, Region);

      declare
         S : String (1 .. Integer (Length (File)));
         for S'Address use Data (Region).all'Address;
         --  A fake string directly mapped onto the file contents

      begin
         GNAT.SHA1.Update (C, S);
      end;

      Free (Region);

      Close (File);
   end Hash_File;

   -----------------
   -- Init_Client --
   -----------------

   function Init_Client return Cache_Client.Cache'Class is
      Info  : String renames Argument (2);
      Colon : constant Natural :=
        Ada.Strings.Fixed.Index (Info, ":");

      Wrong_Port_Msg : constant String :=
        ("port value should be an integer between 1 and 65535");

   begin
      if Colon = 0 then
         Report_Error
           ("the expected format of option --memcached-server " &
              "is hostname:portnumber, but no colon was found");
      end if;
      declare
         First  : String renames Info (Info'First .. Colon - 1);
         Second : String renames Info (Colon + 1 .. Info'Last);
      begin
         if First'Length = 4 and then First = "file" then
            if not Ada.Directories.Exists (Second) then
               Report_Error ("file caching: no such directory: " & Second);
            end if;
            return Filecache_Client.Init (Second);
         else
            declare
               Port     : constant Port_Type :=
                 Port_Type'Value (Info (Colon + 1 .. Info'Last));
            begin
               if Port = No_Port then
                  Report_Error (Wrong_Port_Msg);
               else
                  return Memcache_Client.Init (First, Port);
               end if;
            exception
               when Constraint_Error => Report_Error (Wrong_Port_Msg);
            end;
         end if;
      end;
   end Init_Client;

   ------------------
   -- Report_Error --
   ------------------

   procedure Report_Error (Msg : String) is
      Res : constant JSON_Value := Create_Object;
   begin
      --  Currently, gnatwhy3 is the only program to be wrapped by this
      --  wrapper. Therefore we can emulate it's output in case of error. This
      --  is done here by creating a JSON record with the error message. See
      --  why3/src/gnat/gnat_report.mli for the format of this output.

      Set_Field (Res, "error", Msg);
      Set_Field (Res, "internal", Create (False));
      Set_Field (Res, "results", Create (Empty_Array));
      Ada.Text_IO.Put_Line (Write (Res));
      GNAT.OS_Lib.OS_Exit (1);
   end Report_Error;

   -----------------
   -- Compute_Key --
   -----------------

   function Compute_Key return GNAT.SHA1.Message_Digest is
      C : GNAT.SHA1.Context := GNAT.SHA1.Initial_Context;
   begin

      --  We first hash the salt (first argument of the command line)

      GNAT.SHA1.Update (C, Argument (1));

      --  The file is hashed separately here, it always comes last on the
      --  command line.

      Hash_File (C, Argument (Argument_Count));

      --  Hash the rest of the command line

      Hash_Commandline (C);

      --  Read the binary hash if present

      if Argument_Count >= 3 then
         Hash_Binary (C, Argument (3));
      end if;
      return GNAT.SHA1.Digest (C);
   end Compute_Key;

begin

   --  We need this extra declare block so that the declarations are executed
   --  in the scope of the exception handler below.

   declare
      Cache : Cache_Client.Cache'Class := Init_Client;

      Key : constant String := Compute_Key;
      Msg : constant String := Cache.Get (Key);
      Status : aliased Integer := 0;
   begin
      if Msg'Length /= 0 then
         Ada.Text_IO.Put_Line (Msg);
      else
         declare
            Arguments : Argument_List (1 .. Argument_Count - 3);
         begin
            for I in Arguments'Range loop
               Arguments (I) := new String'(Argument (I + 3));
            end loop;
            declare
               Cmd : String renames Argument (3);

               Msg : constant String :=
                 Get_Command_Output (Cmd,
                                     Arguments,
                                     "",
                                     Status'Access,
                                     Err_To_Out => True);
            begin

               --  We don't want to cache crashes of gnatwhy3; also we know
               --  that gnatwhy3 returns 0 in normal execution. Other processes
               --  may return non-zero exit code and we still want to cache
               --  them.

               if Status = 0 or else Cmd /= "gnatwhy3" then
                  Cache.Set (Key, Msg);
               end if;
               Ada.Text_IO.Put_Line (Msg);
            end;
         end;
      end if;
      Cache.Close;
      GNAT.OS_Lib.OS_Exit (Status);
   end;
exception
   when Error : GNAT.Sockets.Socket_Error =>
      Report_Error (Ada.Exceptions.Exception_Message (Error));
end SPARK_Memcached_Wrapper;
