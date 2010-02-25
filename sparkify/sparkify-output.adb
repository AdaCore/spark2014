------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                       S P A R K I F Y . O U T P U T                      --
--                                                                          --
--                                 B o d y                                  --
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

with Ada.Characters.Handling;          use Ada.Characters.Handling;
with Ada.Sequential_IO;
with Ada.Text_IO;
with Ada.Wide_Text_IO;                 use Ada.Wide_Text_IO;
with Ada.Directories;                  use Ada.Directories;

with GNAT.OS_Lib;                      use GNAT.OS_Lib;

with Hostparm;

with ASIS_UL.Options;                  use ASIS_UL.Options;
with ASIS_UL.Output;                   use ASIS_UL.Output;

with Sparkify.Options;                 use Sparkify.Options;
with Sparkify.State;                   use Sparkify.State;
with Sparkify.Basic;                   use Sparkify.Basic;

package body Sparkify.Output is

   Out_Suffix : String_Access;
   pragma Unreferenced (Out_Suffix);
   --  The suffix of the file to put the pretty-printed source in

   Backup_Suffix : String_Access;
   --  The suffix of the file to put the back-up copy of the argument source
   --  in case if we rewrite it with the pretty-printed source.

   package Char_Sequential_IO is new Ada.Sequential_IO (Character);
   --  Used by the Correct_EOL text filter

   Filter_Tmp_FD   : GNAT.OS_Lib.File_Descriptor;
   Filter_Tmp_Name : GNAT.OS_Lib.Temp_File_Name;
   Filter_Tmp_Seq_FD : Char_Sequential_IO.File_Type;
   --  Temporary file where Correct_EOL writes the copy of the result source
   --  with the corrected line ends. The only reason to use the file stuff from
   --  GNAT.OS_lib is to get the temporary file name.

   Result_FD         : Ada.Text_IO.File_Type;
   --  The same as Result_Out_File, but viewed by Ada.Text_IO, not
   --  Ada.Wide_Text_IO;

   Tmp_Line_Buf : String (1 .. Max_Line_Length);
   Tmp_Line_Len : Natural range 0 .. Max_Line_Length;
   --  Buffer to read one line of the result file. Note that we use
   --  Sparkify.Options.Max_Line_Length, so in any case this buffer will have
   --  enough room for a line read from the result file.

   ----------------
   -- Brief_Help --
   ----------------

   procedure Brief_Help is
      Tmp_Output : constant File_Access := Current_Output;
   begin
      Set_Output (Standard_Error);

      Put ("usage: sparkify [options] {filename} ");
      Put ("[gcc_switches]");
      New_Line;
      Put (" options (in alphabetic order):");
      New_Line;

      Put (" -gnatec<path> - the same as GNAT -gnatec option");
      New_Line;

      Put (" -I<dir> - the same as gcc -I option");
      New_Line;

      Put (" -I-     - the same as gcc -I- option");
      New_Line;

      Put (" --RTS=<dir> - the same as gcc --RTS option");
      New_Line;

      Put (" -q  - quiet mode");
      New_Line;

      Put (" -v  - verbose mode");
      New_Line;

      Put (" -w  - warnings ON");
      New_Line;
      New_Line;

      New_Line;
      Put ("Output file control:");
      New_Line;
      Put (" -pipe - send the output into Stdout");
      New_Line;
      Put (" -o output_file - write the output into output_file. Give up if ");
      Put ("output_file");
      New_Line;
      Put ("                  already exists");
      New_Line;
      Put (" -of output_file - write the output into output_file, overriding");
      Put (" the existing ");
      New_Line;
      Put ("                   file");
      New_Line;
      Put (" -r   - replace the argument source with the pretty-printed");
      Put (" source and copy the");
      New_Line;
      Put ("        argument source into filename" &
                  To_Wide_String (NPP_Suffix));
      Put (". Give up if filename" & To_Wide_String (NPP_Suffix));
      New_Line;
      Put ("        already exists");
      New_Line;
      Put (" -rf  - replace the argument source with the pretty-printed ");
      Put ("source and copy the");
      New_Line;
      Put ("        argument source into filename" &
                   To_Wide_String (NPP_Suffix));
      Put (" , overriding the existing file");
      New_Line;

      Put (" -rnb - replace the argument source with the pretty-printed ");
      Put ("source and do not");
      New_Line;
      Put ("        create the back-up copy of the argument source");
      New_Line;

      New_Line;
      Put (" filename - the name of the Ada source file to be reformatted. ");
      New_Line;
      Put ("            Wildcards are allowed");
      New_Line;
      Put (" --eol=text_format - sets the format of the sparkify output " &
           "file(s),");
      New_Line;
      Put ("                    can not be used together with -pipe option");
      New_Line;
      Put ("       text_format can be - 'unix' or 'lf'   - lines end with " &
           "LF character");
      New_Line;
      Put ("                          - 'dos'  or 'crlf' - lines end with " &
           "CRLF characters");
      New_Line;

      Put (" -W(h|u|s|e|8|b) - sets the wide character encoding of the " &
           "result file");
      New_Line;
      Put ("    h - Hex ESC encoding");
      New_Line;
      Put ("    u - Upper half encoding");
      New_Line;
      Put ("    s - Shift-JIS encoding");
      New_Line;
      Put ("    e - EUC Encoding");
      New_Line;
      Put ("    8 - UTF-8 encoding");
      New_Line;
      Put ("    b - Brackets encoding (this is the default)");
      New_Line;

      New_Line;
      Put (" gcc_switches  '-cargs switches' where 'switches' is ");
      Put ("a list of of switches");
      New_Line;
      Put ("               that are valid switches for gcc");
      New_Line;

      Set_Output (Tmp_Output.all);
   end Brief_Help;

   -----------------
   -- Correct_EOL --
   -----------------

   procedure Correct_EOL is
      Success : Boolean;
   begin
      GNAT.OS_Lib.Create_Temp_File
        (FD   => Filter_Tmp_FD,
         Name => Filter_Tmp_Name);

      GNAT.OS_Lib.Close (Filter_Tmp_FD);

      Char_Sequential_IO.Open
        (File => Filter_Tmp_Seq_FD,
         Mode => Char_Sequential_IO.Out_File,
         Name => Filter_Tmp_Name);

      Ada.Text_IO.Open
        (File => Result_FD,
         Mode => Ada.Text_IO.In_File,
         Name => Res_File_Name.all);

      while not Ada.Text_IO.End_Of_File (Result_FD) loop

         Ada.Text_IO.Get_Line
           (File => Result_FD,
            Item => Tmp_Line_Buf,
            Last => Tmp_Line_Len);

         for J in 1 .. Tmp_Line_Len loop
            Char_Sequential_IO.Write
              (File => Filter_Tmp_Seq_FD,
               Item => Tmp_Line_Buf (J));
         end loop;

         case Out_File_Format is
            when Default =>
               pragma Assert (False);
               null;
            when CRLF =>
               Char_Sequential_IO.Write
                 (File => Filter_Tmp_Seq_FD,
                  Item => ASCII.CR);
               Char_Sequential_IO.Write
                 (File => Filter_Tmp_Seq_FD,
                  Item => ASCII.LF);
            when LF =>
               Char_Sequential_IO.Write
                 (File => Filter_Tmp_Seq_FD,
                  Item => ASCII.LF);
         end case;

      end loop;

      Char_Sequential_IO.Close (File => Filter_Tmp_Seq_FD);

      Ada.Text_IO.Close (File => Result_FD);

      if Hostparm.OpenVMS then
         Copy_File
           (Name     => Filter_Tmp_Name,
            Pathname => Res_File_Name.all,
            Success  => Success,
            Mode     => Overwrite,
            Preserve => None);

      else
         Copy_File
           (Name     => Filter_Tmp_Name,
            Pathname => Res_File_Name.all,
            Success  => Success,
            Mode     => Overwrite);
      end if;

      if not Success then
         Put (Standard_Error, "sparkify: can not convert the line ends for ");
         Put (Standard_Error, To_Wide_String (Res_File_Name.all));
         New_Line (Standard_Error);
      end if;

      GNAT.OS_Lib.Delete_File (Filter_Tmp_Name, Success);

      if not Success then
         Put (Standard_Error, "sparkify: can not delete the line end ");
         Put (Standard_Error, "filter temp file");
         New_Line (Standard_Error);
      end if;

   end Correct_EOL;

   ----------------
   -- NPP_Suffix --
   ----------------

   function NPP_Suffix return String is
   begin

      if Hostparm.OpenVMS then
         return "$NPP";
      else
         return ".npp";
      end if;

   end NPP_Suffix;

   ---------------
   -- PP_Suffix --
   ---------------

   function PP_Suffix  return String is
   begin

      if Hostparm.OpenVMS then
         return "$PP";
      else
         return ".pp";
      end if;

   end PP_Suffix;

   ---------------------
   -- Set_Form_String --
   ---------------------

   procedure Set_Form_String is
   begin

      case Output_Encoding is
         when Hex_ESC =>
            Free (Form_String);
            Form_String := new String'("WCEM=h");
         when Upper_Half =>
            Free (Form_String);
            Form_String := new String'("WCEM=u");
         when Shift_JIS =>
            Free (Form_String);
            Form_String := new String'("WCEM=s");
         when EUC =>
            Free (Form_String);
            Form_String := new String'("WCEM=e");
         when UTF_8 =>
            Free (Form_String);
            Form_String := new String'("WCEM=8");
         when Brackets =>
            Free (Form_String);
            Form_String := new String'("WCEM=b");
         when Default =>
            null;
      end case;

   end Set_Form_String;

   ----------------
   -- Set_Output --
   ----------------

   procedure Set_Output (SF : SF_Id; Success : out Boolean) is
   begin

      Success := True;

      if Output_Mode not in Replace .. Replace_No_Backup then
         Free (Res_File_Name);
      end if;

      case Output_Mode is
         when Pipe =>
            null;
         when Create_File .. Force_Create_File  =>
            --  Can be only if we have only one argument source
            --  All the checks and settings are made in
            --  Sparkify.Environment.Check_Parameters
            null;

         when Replace .. Replace_No_Backup =>

            if Output_Mode = Replace and then
               Is_Regular_File (Source_Name (SF) & Backup_Suffix.all)
            then
               Put (Standard_Error, "sparkify: file ");
               Put (Standard_Error, To_Wide_String (Res_File_Name.all));
               Put (Standard_Error, " exists. Use '-rf' option to override");
               New_Line (Standard_Error);
               Success := False;
            end if;

            if Success and then Output_Mode /= Replace_No_Backup then

               if Verbose_Mode then
                  Put (Standard_Error, "sparkify: creating the back-up copy ");
                  Put (Standard_Error, "of the original source");
                  Put (Standard_Error, To_Wide_String (Source_Name (SF)));
                  New_Line (Standard_Error);
               end if;

               if Hostparm.OpenVMS then
                  Copy_File
                    (Name     => Source_Name (SF),
                     Pathname => Source_Name (SF) & Backup_Suffix.all,
                     Success  => Success,
                     Mode     => Overwrite,
                     Preserve => None);

               else
                  Copy_File
                    (Name     => Source_Name (SF),
                     Pathname => Source_Name (SF) & Backup_Suffix.all,
                     Success  => Success,
                     Mode     => Overwrite);
               end if;

               if not Success then
                  Put (Standard_Error, "sparkify: can not create ");
                  Put (Standard_Error, "the back-up copy for ");
                  Put (Standard_Error, To_Wide_String (Source_Name (SF)));
                  New_Line (Standard_Error);
               end if;

            end if;

         when Default =>
            declare
               Source_Dir_Name : constant String :=
                 Containing_Directory (Source_Name (SF));
               Dir_Name : constant String :=
                 Compose (Source_Dir_Name, Out_Dirname);
               File_Name : constant String :=
                 Compose (Dir_Name, Short_Source_Name (SF));
            begin
               if not Ada.Directories.Exists (Dir_Name) then
                  --  Create directory for output
                  Ada.Directories.Create_Directory (Dir_Name);
               else
                  pragma Assert (Kind (Dir_Name) = Directory);
                  null;
               end if;

--            Res_File_Name := new String'(Source_Name (SF) & Out_Suffix.all);

               Res_File_Name := new String'(File_Name);
               Out_File_Exists := Is_Regular_File (Res_File_Name.all);
            end;
      end case;

      if Success
        and then
         Output_Mode /= Pipe
        and then
         Output_Mode not in Create_File .. Force_Create_File
      then

         if Out_File_Exists then
            Open (File => Result_Out_File,
                  Mode => Out_File,
                  Name => Res_File_Name.all,
                  Form => Form_String.all);
         else
            Create (File => Result_Out_File,
                    Mode => Out_File,
                    Name => Res_File_Name.all,
                    Form => Form_String.all);
         end if;

      end if;

      if Output_Mode = Pipe then
         Set_Output (Ada.Wide_Text_IO.Standard_Output);
      elsif Success then
         Set_Output (Result_Out_File);
      end if;

   exception
      when Ada.Wide_Text_IO.Status_Error =>
         Put (Standard_Error, "sparkify: can not write in ");

         if Res_File_Name /= null then
            Put (Standard_Error, To_Wide_String (Res_File_Name.all));
         end if;

         New_Line (Standard_Error);

         Put (Standard_Error, "the file is probably in use");
         New_Line (Standard_Error);

         Success := False;

         --  ??? Source file status

      when Ada.Wide_Text_IO.Name_Error | Ada.Wide_Text_IO.Use_Error =>
         Put (Standard_Error, "sparkify: can not write in ");

         if Res_File_Name /= null then
            Put (Standard_Error, To_Wide_String (Res_File_Name.all));
         end if;

         New_Line (Standard_Error);
         Put (Standard_Error, "check the file name");
         New_Line (Standard_Error);

         Success := False;

         --  ??? Source file status

      when Ex : others =>
         Report_Unhandled_Exception (Ex);

         Success := False;

         --  ??? Source file status

   end Set_Output;

begin
   Out_Suffix    := new String'(PP_Suffix);
   Backup_Suffix := new String'(NPP_Suffix);
end Sparkify.Output;
