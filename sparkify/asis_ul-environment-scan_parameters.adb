------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--  A S I S _ U L . E N V I R O N M E N T . S C A N _ P A R A M E T E R S   --
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

with GNAT.Command_Line;                use GNAT.Command_Line;

with ASIS_UL.Compiler_Options;
with ASIS_UL.Options;                  use ASIS_UL.Options;
with ASIS_UL.Source_Table;

with Sparkify.Options;                 use Sparkify.Options;
with Sparkify.Output;                  use Sparkify.Output;
with Sparkify.State;                   use Sparkify.State;

separate (ASIS_UL.Environment)
procedure Scan_Parameters is
   No_More_Args : Boolean := True;
begin
   Warning_Mode := Quiet;
   --  Otherwise an average sparkify run would generate too much diagnoses
   --  about problems in reformatting

   Process_RTL_Units := True;
   --  sparkify does not care about this

   Initialize_Option_Scan
     (Stop_At_First_Non_Switch => True,
      Section_Delimiters       => "cargs");

   loop

      case
         GNAT.Command_Line.Getopt
           ("d dd I: gnatec! -RTS= v w q "       &
            "gnat05 "                            & --  Ada 2005 mode
            "noloc "                             &
            --  output file control
            "-eol= files= pipe o= of= r rf rnb " &
            --  encoding of the result file(s)
            "Wh Wu Ws We W8 Wb")
      is
         when ASCII.NUL =>
            exit;

         when 'd' =>

            if Full_Switch = "d" then
               Debug_Mode := True;
               Compute_Timing := True;
            elsif Full_Switch = "dd" then
               Progress_Indicator_Mode := True;
            end if;

         when 'q' =>
            Quiet_Mode := True;

         when 'r' =>

            if Full_Switch = "r" then
               Output_Mode := Replace;
            elsif Full_Switch = "rnb" then
               Output_Mode := Replace_No_Backup;
            elsif Full_Switch = "rf" then
               Output_Mode := Force_Replace;
            else
               Brief_Help;
               raise Parameter_Error;
            end if;

         when 'I' | 'g' | '-' =>

            if Full_Switch = "I" then
               Store_I_Option (Parameter);
            elsif Full_Switch = "gnatec" then
               Store_GNAT_Option_With_Path (Full_Switch, Parameter);
            elsif Full_Switch = "-RTS" then
               Store_Option ("--RTS=" & Parameter);
            elsif Full_Switch = "-eol" then
               Out_File_Format := Get_Out_File_Format (Parameter);
            elsif Full_Switch = "gnat05" then
               ASIS_UL.Options.ASIS_2005_Mode := True;
            else
               Brief_Help;
               raise Parameter_Error;
            end if;

         when 'n' =>
            if Full_Switch = "noloc" then
               Loc_Mode := False;
            else
               Brief_Help;
               raise Parameter_Error;
            end if;

         when 'o' =>

            if Full_Switch = "o" then
               Output_Mode := Create_File;
            elsif Full_Switch = "of" then
               Output_Mode := Force_Create_File;
            else
               Brief_Help;
               raise Parameter_Error;
            end if;

            Res_File_Name := new String'(Parameter);

         when 'p' =>

            if Full_Switch = "pipe" then
               Output_Mode := Pipe;
            end if;

         when 'v' =>

            Verbose_Mode := True;
            Print_Version_Info (2003);

         when 'W' =>

            if Full_Switch = "Wh" then
               Output_Encoding := Hex_ESC;
            elsif Full_Switch = "Wu" then
               Output_Encoding := Upper_Half;
            elsif Full_Switch = "Ws" then
               Output_Encoding := Shift_JIS;
            elsif Full_Switch = "We" then
               Output_Encoding := EUC;
            elsif Full_Switch = "W8" then
               Output_Encoding := UTF_8;
            elsif Full_Switch = "Wb" then
               Output_Encoding := Brackets;
            else
               Brief_Help;
               raise Parameter_Error;
            end if;

         when 'w' =>

            Warning_Mode := Full;

         when others =>
            Brief_Help;
            raise Parameter_Error;
      end case;

   end loop;

   loop
      Store_Sources_To_Process
        (Get_Argument (Do_Expansion => True), No_More_Args);
      exit when No_More_Args;
   end loop;

   Process_cargs_Section (No_Preprocessing => True);

exception
   when GNAT.Command_Line.Invalid_Switch =>
      Error ("invalid switch : " & Full_Switch);
      Brief_Help;
      raise Parameter_Error;

   when GNAT.Command_Line.Invalid_Parameter =>
      Error ("parameter missed for : -" & Full_Switch);
      Brief_Help;
      raise Parameter_Error;

end Scan_Parameters;
