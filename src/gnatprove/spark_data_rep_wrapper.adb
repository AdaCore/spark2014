------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--              S P A R K _ D A T A _ R E P _ W R A P P E R                 --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2026, AdaCore                         --
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
with Ada.Environment_Variables;
with Ada.Text_IO;
with GNAT.Expect;      use GNAT.Expect;
with GNAT.OS_Lib;      use GNAT.OS_Lib;

procedure SPARK_Data_Rep_Wrapper with No_Return is

   --  This wrapper invokes the compiler (given as its first argument) to
   --  generate data-representation JSON files via -gnatR2js. In normal
   --  mode, all compiler output is suppressed. In verbose mode, compiler
   --  output is printed to stderr so the process manager can capture and
   --  relay it to the caller.
   --
   --  The wrapper always succeeds: if the compiler exits with a non-zero
   --  status, empty JSON files are written so that downstream consumers
   --  always find well-formed (though empty) output. A warning message is
   --  printed to stderr on failure unless quiet mode is active.

   --  Invocation:
   --  spark_data_rep_wrapper <compiler> <args...>
   --
   --  <compiler> is the Ada compiler executable (e.g. gcc).
   --  <args...>  are the arguments forwarded verbatim to the compiler.
   --
   --  The following environment variables control wrapper behaviour:
   --
   --  SPARK_DATA_REP_VERBOSITY   "quiet", "normal" (default), or "verbose"
   --  SPARK_DATA_REP_BODY_JSON   path to the expected body (or spec-only)
   --                             JSON output file
   --  SPARK_DATA_REP_SPEC_JSON   path to the expected spec JSON output file;
   --                             set only when the unit has both a body and
   --                             a spec

   --  Design decisions:
   --
   --  Always exits with success: the wrapper always returns 0 regardless of
   --  whether the compiler succeeded. Data-representation information is an
   --  optional input to analysis, so a failure here must not block subsequent
   --  steps. On failure, an empty JSON file is written instead so that
   --  downstream consumers always find a well-formed (though empty) file.
   --
   --  GCC generates JSON data even in case of a compilation failure. The
   --  wrapper therefore only writes the fallback file if the expected output
   --  was not produced by the compiler. This also requires deleting the
   --  file before invoking the compiler.

   type Verbosity_Level is (Quiet, Normal, Verbose);

   function Get_Verbosity return Verbosity_Level;
   --  Read the verbosity level from SPARK_DATA_REP_VERBOSITY

   procedure Write_Empty_JSON (Path : String);
   --  Write an empty JSON array to the file at Path

   procedure Delete_If_Present (Path : String);
   --  Delete the file at Path if it exists

   Status   : aliased Integer := 0;
   Compiler : String_Access;

   Args :
     String_List (1 .. (if Argument_Count > 1 then Argument_Count - 1 else 0));

   Body_JSON : constant String :=
     Ada.Environment_Variables.Value ("SPARK_DATA_REP_BODY_JSON", "");

   Spec_JSON : constant String :=
     Ada.Environment_Variables.Value ("SPARK_DATA_REP_SPEC_JSON", "");

   -------------------
   -- Get_Verbosity --
   -------------------

   function Get_Verbosity return Verbosity_Level is
      V : constant String :=
        Ada.Environment_Variables.Value ("SPARK_DATA_REP_VERBOSITY", "normal");
   begin
      if V = "verbose" then
         return Verbose;
      elsif V = "quiet" then
         return Quiet;
      else
         return Normal;
      end if;
   end Get_Verbosity;

   ----------------------
   -- Write_Empty_JSON --
   ----------------------

   procedure Write_Empty_JSON (Path : String) is
      File : Ada.Text_IO.File_Type;
   begin
      Ada.Text_IO.Create (File, Ada.Text_IO.Out_File, Path);
      Ada.Text_IO.Put (File, "[]");
      Ada.Text_IO.Close (File);
   end Write_Empty_JSON;

   -----------------------
   -- Delete_If_Present --
   -----------------------

   procedure Delete_If_Present (Path : String) is
   begin
      if Ada.Directories.Exists (Path) then
         Ada.Directories.Delete_File (Path);
      end if;
   end Delete_If_Present;

   Verbosity : constant Verbosity_Level := Get_Verbosity;

begin
   if Argument_Count < 1 then
      OS_Exit (0);
   end if;

   Compiler := Locate_Exec_On_Path (Argument (1));

   for I in 2 .. Argument_Count loop
      Args (I - 1) := new String'(Argument (I));
   end loop;

   --  Remove any stale JSON files from a previous run so downstream consumers
   --  see only fresh output.
   if Body_JSON /= "" then
      Delete_If_Present (Body_JSON);
   end if;
   if Spec_JSON /= "" then
      Delete_If_Present (Spec_JSON);
   end if;

   --  Run the compiler, capturing all output (stdout and stderr merged).
   --  In verbose mode the output is printed to stderr so the process
   --  manager can relay it; otherwise it is discarded.
   if Compiler /= null then
      declare
         Output : constant String :=
           Get_Command_Output
             (Compiler.all, Args, "", Status'Access, Err_To_Out => True);
      begin
         if Verbosity = Verbose and then Output /= "" then
            Ada.Text_IO.Put (Ada.Text_IO.Standard_Error, Output);
         end if;
      end;
   end if;

   --  On compiler failure, warn and write empty JSON files for the expected
   --  outputs so that downstream consumers always find valid (though empty)
   --  JSON.
   if (Compiler = null or else Status /= 0) and then Body_JSON /= "" then
      if Verbosity /= Quiet then
         Ada.Text_IO.Put_Line
           (Ada.Text_IO.Standard_Error,
            "warning: data representation info unavailable for "
            & Ada.Directories.Base_Name
                (Ada.Directories.Simple_Name (Body_JSON)));
      end if;

      --  Write a fallback only if the compiler did not produce the file
      --  despite the non-zero exit code.
      if not Ada.Directories.Exists (Body_JSON) then
         Write_Empty_JSON (Body_JSON);
      end if;

      if Spec_JSON /= "" and then not Ada.Directories.Exists (Spec_JSON) then
         Write_Empty_JSON (Spec_JSON);
      end if;
   end if;

   OS_Exit (0);
end SPARK_Data_Rep_Wrapper;
