------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--  S P A R K I F Y . P R O C E S S I N G . P R E P A R E _ C O N T E X T   --
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

--  This version of Prepare_Context is supposed to be used for the non
--  GNSA-based sparkify version

with Asis.Ada_Environments;    use Asis.Ada_Environments;
with Asis.Errors;
with Asis.Exceptions;          use Asis.Exceptions;

with ASIS_UL.Common;
with ASIS_UL.Compiler_Options; use ASIS_UL.Compiler_Options;

separate (Sparkify.Processing)
procedure Prepare_Context (SF : SF_Id; Success : out Boolean) is
   use type Asis.Errors.Error_Kinds;
begin

   Compile
     (new String'(Source_Name (SF)),
      Arg_List.all,
      Success,
      GCC => ASIS_UL.Common.Gcc_To_Call);

   if Success then

      Associate (The_Context => The_Context,
                 Name        => "",
                 Parameters  =>
                  "-C1 " & To_Wide_String (Suffixless_Name (SF) & ".adt"));

      Open (The_Context);
   end if;

exception
   when Program_Error =>
      raise;

   when Ex : ASIS_Failed =>
      --  The only known situation when we can not open a C1 context for
      --  newly created tree is recompilation of System (see D617-017)

      if Asis.Implementation.Status = Asis.Errors.Use_Error
        and then
         Asis.Implementation.Diagnosis =
         "Cannot process Ada sources compiled with -gnat05"
      then
         --  EC12-013: This path should be removed when ASIS 2005 is
         --  implemented
         Put_Line ("sparkify: Ada 2005 not supported yet, exiting");
         raise Fatal_Error;

      elsif Asis.Implementation.Status = Asis.Errors.Use_Error
        and then
         Asis.Implementation.Diagnosis = "Internal implementation error:"
         & " Asis.Ada_Environments.Open - System is recompiled"
      then
         Put (Standard_Error, "sparkify: can not process redefinition of " &
                 "System in "& Source_Name (SF));
         New_Line (Standard_Error);
         Success := False;
      else
         Put (Standard_Error,
              "sparkify: unexpected bug when opening a context");
         Put ("(" & Source_Name (SF) & ")");
         New_Line (Standard_Error);
         Report_Unhandled_ASIS_Exception (Ex);
         raise Fatal_Error;
      end if;

   when Ex : others =>
      Put (Standard_Error, "sparkify: unexpected bug when opening a context");
      Put ("(" & Source_Name (SF) & ")");
      New_Line (Standard_Error);
      Report_Unhandled_Exception (Ex);
      raise Fatal_Error;
end Prepare_Context;
