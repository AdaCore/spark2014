------------------------------------------------------------------------------
--                                                                          --
--                           GNATPROVE COMPONENTS                           --
--                                                                          --
--          G P R C O N F I G _ M E M C A C H E D _ W R A P P E R           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2020, AdaCore, Altran UK                  --
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
with Ada.Directories;  use Ada.Directories;
with Ada.Text_IO;
with GNAT.OS_Lib;      use GNAT.OS_Lib;
with GNAT.SHA1;
with GNAT.Sockets;     use GNAT.Sockets;
with GNATCOLL.Mmap;
with GNATCOLL.Utils;
with Memcache_Client;

procedure GPRConfig_Memcached_Wrapper is

   --  This is a wrapper, which caches identical invocations of gprconfig by
   --  hashing the input to the tool (commandline but not input files), and
   --  compares this hash with previous runs of gprconfig. If a match is
   --  found, the output of the previous run is output.

   --  It prevents repeated invocations of gprconfig when running the spark2014
   --  testsuite. Such invocations are quite slow, because gprconfig parses its
   --  XML configuration files.

   --  Note: this tool may cause setup problems; it must be used by with care.
   --  To enable it, rename the resulting binary to 'gprconfig' and put it on
   --  your PATH. It assumes that the original gprconfig executable is located
   --  in the same directory as 'gprls'.

   --  Invocation:
   --  gprconfig <args>

   --------------
   -- Settings --
   --------------

   Hostname : constant String    := "localhost";
   Port     : constant Port_Type := 11211;
   --  Memcache server location
   --  ??? if needed, these could be taken from environmental variables

   function Compute_Key return GNAT.SHA1.Message_Digest;
   --  @return key for caching the results

   function GPRConfig_Path return String;
   --  @return location of the original gprconfig executable

   procedure Hash_Commandline (C : in out GNAT.SHA1.Context);
   --  @param C the hash context to be updated
   --  Compute a hash of the commandline provided to the wrapper

   function Output_File return String;
   --  @return name of the file given with the -o command line argument or
   --    an empty string if no -o switch is present

   function Spawn_Gprconfig return Integer;
   --  @return status returned by executing the original gprconfig utility

   -----------------
   -- Compute_Key --
   -----------------

   function Compute_Key return GNAT.SHA1.Message_Digest is
      C : GNAT.SHA1.Context := GNAT.SHA1.Initial_Context;
   begin
      Hash_Commandline (C);
      return GNAT.SHA1.Digest (C);
   end Compute_Key;

   --------------------
   -- GPRConfig_Path --
   --------------------

   function GPRConfig_Path return String is
      Sibling_Path : String_Access := Locate_Exec_On_Path ("gprls");

   begin
      if Sibling_Path = null then
         raise Program_Error;
      else
         declare
            GPRConfig_Dir : constant String :=
              Containing_Directory (Sibling_Path.all);
         begin
            Free (Sibling_Path);

            return Compose (GPRConfig_Dir, "gprconfig");
         end;
      end if;
   end GPRConfig_Path;

   ----------------------
   -- Hash_Commandline --
   ----------------------

   procedure Hash_Commandline (C : in out GNAT.SHA1.Context) is
      J : Positive := 1;

      Last_Arg : constant Natural := Ada.Command_Line.Argument_Count;

   begin
      while J <= Last_Arg loop
         declare
            Arg : constant String := Ada.Command_Line.Argument (J);
         begin
            --  Ignore both -o and the following argument
            if Arg = "-o" then
               J := J + 2;
            else
               GNAT.SHA1.Update (C, Arg);
               J := J + 1;
            end if;
         end;
      end loop;
   end Hash_Commandline;

   -----------------
   -- Output_File --
   -----------------

   function Output_File return String is
   begin
      for J in 2 .. Ada.Command_Line.Argument_Count loop
         if Ada.Command_Line.Argument (J) = "-o" then
            return Ada.Command_Line.Argument (J + 1);
         end if;
      end loop;

      return "";
   end Output_File;

   ---------------------
   -- Spawn_Gprconfig --
   ---------------------

   function Spawn_Gprconfig return Integer is
      Arguments : Argument_List (1 .. Argument_Count);
      --  Command and arguments for the call to original gprconfig

      Status : Integer;

   begin
      for I in Arguments'Range loop
         Arguments (I) := new String'(Argument (I));
      end loop;

      Status := GNAT.OS_Lib.Spawn (Program_Name => GPRConfig_Path,
                                   Args         => Arguments);

      GNATCOLL.Utils.Free (Arguments);

      return Status;
   end Spawn_Gprconfig;

   Output_Filename : constant String := Output_File;

--  Start of processing for GPRConfig_Memcache_Wrapper

begin
   --  Do not cache invocations unless the -o switch is present

   if Output_Filename'Length = 0 then
      OS_Exit (Spawn_Gprconfig);
   else
      declare
         Cache : Memcache_Client.Cache_Connection :=
           Memcache_Client.Init (Hostname, Port);

         Key : constant String := Compute_Key & "_gprconfig";
         --  A human-readable suffix helps to identify keys from this wrapper

         Response : constant String := Memcache_Client.Get (Cache, Key);

         Status : Integer;

      begin
         --  If no key was found, then invoke gprconfig as usual and cache its
         --  output.
         if Response'Length = 0 then
            Status := Spawn_Gprconfig;

            --  Ignore failures and cache only successful invocations
            if Status = 0 then

               Read_File : declare
                  use GNATCOLL.Mmap;
                  File   : Mapped_File;
                  Region : Mapped_Region;

               begin
                  File := Open_Read (Output_Filename);

                  Read (File, Region);

                  declare
                     S : String (1 .. Integer (Length (File)));
                     for S'Address use Data (Region).all'Address;
                     --  A fake string directly mapped onto the file contents

                  begin
                     Memcache_Client.Set (Cache, Key, S);
                  end;

                  Free (Region);

                  Close (File);
               end Read_File;
            end if;

         --  Otherwise, write the server's response into file and return a
         --  success (which is fine, because we only cache successful
         --  invocations).

         else
            Status := 0;

            Write_File : declare
               Output : Ada.Text_IO.File_Type;
            begin
               Ada.Text_IO.Create (File => Output, Name => Output_Filename);
               Ada.Text_IO.Put (Output, Response);
               Ada.Text_IO.Close (Output);
            end Write_File;
         end if;

         Memcache_Client.Close (Cache);

         OS_Exit (Status);
      end;
   end if;
end GPRConfig_Memcached_Wrapper;
