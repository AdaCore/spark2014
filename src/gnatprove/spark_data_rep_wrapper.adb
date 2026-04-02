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
with Ada.Text_IO;
with GNAT.Expect;      use GNAT.Expect;
with GNAT.OS_Lib;      use GNAT.OS_Lib;

procedure SPARK_Data_Rep_Wrapper with No_Return is

   --  This wrapper invokes the compiler (given as its first argument) to
   --  generate data-representation JSON files via -gnatR2js.  In normal
   --  mode, all compiler output is suppressed.  When --verbose is present
   --  in the argument list, compiler output is printed to stderr so the
   --  process manager can capture and relay it to the caller.
   --
   --  The wrapper always succeeds: if the compiler exits with a non-zero
   --  status, empty JSON files are written so that downstream consumers
   --  always find well-formed (though empty) output.  A warning message is
   --  printed to stderr on failure regardless of the verbose flag.

   --  Invocation:
   --  spark_data_rep_wrapper <compiler> [--verbose] [--quiet] <args...>
   --  (--verbose and --quiet may appear anywhere in the argument list and
   --   won't be forwarded to the compiler)

   --  <compiler> is the Ada compiler executable (e.g. gcc).
   --  <args...>  are the arguments forwarded verbatim to the compiler.

   --  Design decisions:
   --
   --  Always exits with success: the wrapper always returns 0 regardless of
   --  whether the compiler succeeded.  Data-representation information is an
   --  optional input to analysis, so a failure here must not block subsequent
   --  steps.  On failure, an empty JSON file is written instead so that
   --  downstream consumers always find a well-formed (though empty) file.
   --
   --  GCC generates JSON data even in case of a compilation failure. The
   --  wrapper therefore only writes the fallback empty file if the expected
   --  output file was not produced by the compiler. This also requires
   --  us to delete the file before the compiler is invoked.

   Status  : aliased Integer := 0;
   Verbose : Boolean := False;
   Quiet   : Boolean := False;

   --  Resolve the compiler executable given as the first argument
   Compiler : String_Access;

   --  Build the argument list for the compiler: everything after arg 1,
   --  minus --verbose.  We over-allocate by one; Arg_Last tracks the
   --  actual count.
   Args     :
     String_List (1 .. (if Argument_Count > 0 then Argument_Count - 1 else 0));
   Arg_Last : Natural := 0;

   --  Paths recovered by scanning the argument list, used for error recovery
   Source_File : String_Access;
   Output_File : String_Access;

   --  JSON output paths, computed after argument scanning
   Body_JSON : String_Access;
   Spec_JSON : String_Access;

   procedure Write_Empty_JSON (Path : String);
   --  Write an empty JSON array to the file at Path, silently ignoring any
   --  I/O errors.

   procedure Delete_If_Present (Path : String);
   --  Delete the file at Path if it exists, silently ignoring any I/O errors

   -----------------------
   -- Write_Empty_JSON  --
   -----------------------

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

begin
   if Argument_Count < 1 then
      OS_Exit (0);
   end if;

   Compiler := Locate_Exec_On_Path (Argument (1));

   --  Build the compiler argument list, detecting --verbose and --quiet along
   --  the way.

   for I in 2 .. Argument_Count loop
      if Argument (I) = "--verbose" then
         Verbose := True;
      elsif Argument (I) = "--quiet" then
         Quiet := True;
      else
         Arg_Last := Arg_Last + 1;
         Args (Arg_Last) := new String'(Argument (I));
      end if;
   end loop;

   --  Scan compiler arguments to locate the source file and the -o output
   --  path; both are needed to derive the JSON output paths on failure.

   declare
      I : Positive := 1;
   begin
      while I <= Arg_Last loop
         declare
            Arg : constant String := Args (I).all;
         begin
            if Arg = "-o" and then I < Arg_Last then
               Output_File := new String'(Args (I + 1).all);
               I := I + 2;
            elsif Arg'Length > 0
              and then Arg (Arg'First) /= '-'
              and then Ada.Directories.Extension (Arg) in "adb" | "ads"
            then
               Source_File := new String'(Arg);
               I := I + 1;
            else
               I := I + 1;
            end if;
         end;
      end loop;
   end;

   --  Compute the expected JSON output paths, then remove any stale files
   --  from a previous run so downstream consumers see only fresh output.

   if Source_File /= null then
      declare
         Src_Name : constant String :=
           Ada.Directories.Simple_Name (Source_File.all);
         Ext      : constant String := Ada.Directories.Extension (Src_Name);
         Out_Dir  : constant String :=
           (if Output_File /= null
            then Ada.Directories.Containing_Directory (Output_File.all)
            else Ada.Directories.Current_Directory);
      begin
         Body_JSON :=
           new String'(Ada.Directories.Compose (Out_Dir, Src_Name & ".json"));
         Delete_If_Present (Body_JSON.all);

         if Ext = "adb" then
            Spec_JSON :=
              new String'
                (Ada.Directories.Compose
                   (Out_Dir,
                    Ada.Directories.Base_Name (Src_Name) & ".ads.json"));
            Delete_If_Present (Spec_JSON.all);
         end if;
      end;
   end if;

   --  Run the compiler, capturing all output (stdout and stderr merged).
   --  In verbose mode the output is printed to stderr so the process
   --  manager can relay it; otherwise it is discarded.

   if Compiler /= null then
      declare
         Output : constant String :=
           Get_Command_Output
             (Compiler.all,
              Args (1 .. Arg_Last),
              "",
              Status'Access,
              Err_To_Out => True);
      begin
         if Verbose and then Output /= "" then
            Ada.Text_IO.Put (Ada.Text_IO.Standard_Error, Output);
         end if;
      end;
   end if;

   --  On compiler failure, warn and write empty JSON files for the expected
   --  outputs so that downstream consumers always find valid (though empty)
   --  JSON.

   if (Compiler = null or else Status /= 0) and then Body_JSON /= null then
      if not Quiet then
         Ada.Text_IO.Put_Line
           (Ada.Text_IO.Standard_Error,
            "warning: data representation info unavailable for "
            & Ada.Directories.Simple_Name (Source_File.all));
      end if;

      --  Write a fallback only if the compiler did not produce the file
      --  despite the non-zero exit code.
      if not Ada.Directories.Exists (Body_JSON.all) then
         Write_Empty_JSON (Body_JSON.all);
      end if;

      --  When compiling a body, also cover the spec's JSON output
      if Spec_JSON /= null and then not Ada.Directories.Exists (Spec_JSON.all)
      then
         Write_Empty_JSON (Spec_JSON.all);
      end if;
   end if;

   OS_Exit (0);
end SPARK_Data_Rep_Wrapper;
