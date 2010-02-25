------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
-- A S I S _ U L . E N V I R O N M E N T . C H E C K  _ P A R A M E T E R S --
--                                                                          --
--             (adapted for sparkify from ASIS Utility Library)             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010, AdaCore                        --
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

with Ada.Wide_Text_IO;

with ASIS_UL.Compiler_Options;
with ASIS_UL.Options;                  use ASIS_UL.Options;
with ASIS_UL.Source_Table;

with Sparkify.Basic;                   use Sparkify.Basic;
with Sparkify.Options;                 use Sparkify.Options;
with Sparkify.Output;                  use Sparkify.Output;
with Sparkify.State;                   use Sparkify.State;

separate (ASIS_UL.Environment)
procedure Check_Parameters is
begin
   --  First, read all the argument files using all available path information
   if ASIS_UL.Options.No_Argument_File_Specified then
      Error ("No input source file set");
      Brief_Help;
      raise Parameter_Error;
   end if;

   Process_ADA_PRJ_INCLUDE_FILE;

   Set_Source_Search_Path;

   Read_Args_From_Temp_Storage (Duplication_Report => True);

   Nothing_To_Do := Last_Source < First_SF_Id;

   if Nothing_To_Do then
      Error ("No existing file to process");
      --  All the rest does not make any sense
      return;
   end if;

   Total_Sources      := Natural (Last_Source);
   Sources_Left       := Total_Sources;

   --  Check that the out file format is not set for the pipe output mode:

   if Output_Mode = Pipe and then Out_File_Format /= Default then
      Put_Line (Standard_Error,
                "sparkify: out file format can not be set in pipe mode");
      Brief_Help;
      raise Parameter_Error;

   end if;

   --  Check that the out file encoding is not set for the pipe output mode,
   --  and set the needed value for the Form parameter for the Create
   --  and Open procedures:

   if Output_Mode = Pipe and then Output_Encoding /= Default then
      Put_Line (Standard_Error,
                "sparkify: out file encoding can not be set in pipe mode");
      Brief_Help;
      raise Parameter_Error;

   elsif Output_Mode /= Pipe then
      Set_Form_String;
   end if;

   if Last_Source = First_SF_Id then
      Multiple_File_Mode := False;

      --  If we have only one source to reformat, we have to check
      --  the settings of the output file, if it is set

      Progress_Indicator_Mode := False;
      --  We do not need this in case of one file, and we may be in the
      --  mode of outputting the reformatted source into Stdout

      Arg_Source_Name := new String'(Source_Name (Last_Source));

      if Output_Mode in Create_File .. Force_Create_File then
         --  We have to set the output file here, before we get into the
         --  temporary directory

         Out_File_Exists := False;

         if Res_File_Name /= null and then
            Is_Regular_File (Res_File_Name.all)
         then

            if Output_Mode = Create_File then
               Put (Standard_Error, "sparkify: file ");
               Put (Standard_Error, Res_File_Name.all);
               Put (Standard_Error, " exists. Use '-of' option");
               Put (Standard_Error, " to override");
               New_Line (Standard_Error);
               raise Parameter_Error;
            else
               Out_File_Exists := True;
            end if;

         end if;

         if Out_File_Exists then
            Ada.Wide_Text_IO.Open
              (File => Result_Out_File,
               Mode => Ada.Wide_Text_IO.Out_File,
               Name => Res_File_Name.all,
               Form => Form_String.all);
         else
            Ada.Wide_Text_IO.Create
              (File => Result_Out_File,
               Mode => Ada.Wide_Text_IO.Out_File,
               Name => Res_File_Name.all,
               Form => Form_String.all);
         end if;

      end if;

   else
      --  If we have more then one file to reformat, we can not have options
      --  '-pipe', '-o' or '-of' set

      Multiple_File_Mode := True;

      if Output_Mode = Pipe then
         Put (Standard_Error, "sparkify: can not send the output ");
         Put (Standard_Error, "into Stdout when multiple ");
         Put (Standard_Error, "argument sources set");
         raise Parameter_Error;

      elsif Output_Mode = Create_File or else
            Output_Mode = Force_Create_File
      then
         Put (Standard_Error, "sparkify: explicit output file name is not ");
         Put (Standard_Error, "allowed when multiple ");
         Put (Standard_Error, "argument sources set");
         raise Parameter_Error;
      end if;

   end if;

   if Output_Mode = Default and then  --  ???
      Arg_Source_Name /= null and then
      Is_Regular_File (Arg_Source_Name.all & PP_Suffix)
   then
      Out_File_Exists := True;
   end if;

   --  Collect all the -I options into the argument list for gcc call

   Set_Arg_List;

end Check_Parameters;
