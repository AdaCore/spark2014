------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                  S P A R K I F Y . P R O C E S S I N G                   --
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

with Ada.Text_IO;                      use Ada.Text_IO;
with Ada.Wide_Text_IO;

with GNAT.OS_Lib;                      use GNAT.OS_Lib;
with Hostparm;

with Asis;                             use Asis;
with Asis.Compilation_Units;           use Asis.Compilation_Units;
--  with Asis.Compilation_Units.Relations;
--  use Asis.Compilation_Units.Relations;
with Asis.Elements;                    use Asis.Elements;
with Asis.Exceptions;
with Asis.Text;                        use Asis.Text;
with Asis.Clauses;                     use Asis.Clauses;

with ASIS_UL.Output;                   use ASIS_UL.Output;

with Sparkify.Basic;                   use Sparkify.Basic;
with Sparkify.Common;                  use Sparkify.Common;
with Sparkify.Names;                   use Sparkify.Names;
with Sparkify.Options;                 use Sparkify.Options;
with Sparkify.Output;                  use Sparkify.Output;
with Sparkify.PP_Output;               use Sparkify.PP_Output;
with Sparkify.Source_Traversal;        use Sparkify.Source_Traversal;
with Sparkify.State;                   use Sparkify.State;
with Sparkify.Cursors;                 use Sparkify.Cursors;

package body Sparkify.Processing is

   ------------------
   -- Pretty_Print --
   ------------------

   procedure Special_Print (Unit : Asis.Compilation_Unit; SF : SF_Id) is
      Program_Unit : constant Asis.Element := Unit_Declaration (Unit);

      Context_Clause : constant Asis.Element_List :=
         Context_Clause_Elements (Unit, True);

      Comp_Pragmas : constant Asis.Element_List := Compilation_Pragmas (Unit);

      First_Pragma_After : Asis.List_Index := Comp_Pragmas'Last + 1;

      Full_Span : constant Asis.Text.Span := Compilation_Span (Program_Unit);
      Unit_Span : constant Asis.Text.Span := Element_Span (Program_Unit);

      Source_Control    : Asis.Traverse_Control  := Asis.Continue;
      Source_State      : Source_Traversal_State := Initial_State;

      Success : Boolean := False;

--        function Body_Unit_From_Declaration
--          (Decl_Unit : Asis.Compilation_Unit) return Asis.Compilation_Unit;
--
--        function Body_Unit_From_Declaration
--          (Decl_Unit : Asis.Compilation_Unit) return Asis.Compilation_Unit
--        is
--           Decl_Unit_List : constant Asis.Compilation_Unit_List :=
--             (1 => Decl_Unit);
--           Body_Unit : constant Asis.Compilation_Unit :=
--             Corresponding_Body (Decl_Unit);
--
--           R : constant Relationship :=
--             Semantic_Dependence_Order
--               (Compilation_Units => Decl_Unit_List,
--                Dependent_Units   => Asis.Nil_Compilation_Unit_List,
--                The_Context       => Enclosing_Context (Decl_Unit),
--                Relation          => Asis.Dependents);
--        begin
--           for Unit_Index in R.Consistent'Range loop
--              declare
--                 Unit : constant Asis.Compilation_Unit :=
--                   R.Consistent (Unit_Index);
--              begin
--                 --  PP_Word (Debug_Image (Unit));
--                 if Is_Equal (Body_Unit, Unit) then
--                    return Unit;
--                 end if;
--              end;
--           end loop;
--           return Asis.Nil_Compilation_Unit;
--        end Body_Unit_From_Declaration;

      Body_Unit : constant Asis.Compilation_Unit := Corresponding_Body (Unit);
      --  Body_Unit_From_Declaration (Unit);

   begin
      Sparkify.State.Initialize;
      Sparkify.Names.Initialize;

      --  Feeding the line table

      Lines_Table.Set_Last (Full_Span.Last_Line);

      Lines_Table.Table (1 .. Full_Span.Last_Line) :=
         Lines_Table.Table_Type
           (Lines (Element    => Program_Unit,
                   First_Line => Full_Span.First_Line,
                   Last_Line  => Full_Span.Last_Line));

      The_Unit := Unit;
      --  To keep the reference to the current unit in a global variable

      The_Last_Line   := Full_Span.Last_Line;
      The_Last_Column := Full_Span.Last_Column;

      --  We separate the following parts of the original source:
      --
      --  1. Lines before the first context clause (if any). These lines may
      --     be either empty lines of comment lines.
      --
      --  2. Context clause (starting from the first context item or pragma
      --     and down to the library item or subunit, including all the
      --     comments in between
      --
      --  3. Library item (or subunit) itself (Unit_Declaration in ASIS
      --     terms)
      --
      --  4. Lines after the end of the end of the Library item (or subunit),
      --     they may be empty lines, comment lines or they may contain
      --     pragmas

      --  Step #1: Lines before the first context clause

      Before_CU := True;

      --  Step #2: Context clause

      Before_CU         := False;
      In_Context_Clause := True;

      for J in Context_Clause'Range loop
         Traverse_Source (Context_Clause (J), Source_Control, Source_State);
      end loop;

      if not Is_Nil (Body_Unit) and then
        not Is_Equal (Body_Unit, Unit) then
         --  Currently processing a package declaration. Get the packages
         --  with'ed in its declaration and its body to generate
         --  a corresponding SPARK inherit clause.
         declare
            Body_Context_Clause : constant Asis.Context_Clause_List :=
              Context_Clause_Elements (Body_Unit, True);
            Both_Context_Clause : constant Asis.Context_Clause_List :=
              Context_Clause & Body_Context_Clause;
            Packages : Nameset.Set := Nameset.Empty_Set;
         begin
            for J in Both_Context_Clause'Range loop
               declare
                  Clause : constant Asis.Element := Both_Context_Clause (J);
               begin
                  if Clause_Kind (Clause) = A_With_Clause then
                     declare
                        Names : constant Asis.Name_List :=
                          Clause_Names (Clause);
                     begin
                        for Name_Idx in Names'Range loop
                           Nameset.Include
                             (Packages,
                              Normalized_Name
                                (Element_Image (Names (Name_Idx))));
                        end loop;
                     end;
                  end if;
               end;
            end loop;

            declare
               Packages_Text : constant Wide_String :=
                 Concat_Names (Packages, ", ");
               Line : constant Line_Number_Positive :=
                 Line_Number_Positive'Max (First_Line_Number (Program_Unit), 2)
                 - 1;
            begin
               if Packages_Text /= "" then
                  PP_Echo_Cursor_Range (Source_State.Echo_Cursor,
                                        Cursor_Before (Program_Unit));
                  PP_Inherit (Line,
                              Element_Span (Program_Unit).First_Column,
                              Packages_Text);
                  Source_State.Echo_Cursor := Cursor_At (Program_Unit);
               end if;
            end;
         end;
      end if;

      --  Step #3: Library item (or subunit) itself

      In_Context_Clause := False;
      In_Unit           := True;

      Traverse_Source (Program_Unit, Source_Control, Source_State);

      --  Step # 4: Lines after the end of the end of the Library item
      --  (or subunit)

      In_Unit     := False;
      Behind_Unit := True;

      for J in Comp_Pragmas'Range loop

         if Unit_Span.Last_Line <=
            Element_Span (Comp_Pragmas (J)).First_Line
         then
            First_Pragma_After := J;
            exit;
         end if;

      end loop;

      for J in First_Pragma_After .. Comp_Pragmas'Last loop

         if Is_Equal (Enclosing_Compilation_Unit (Comp_Pragmas (J)), Unit) then
            --  We may have configuration pragmas in the list
            Traverse_Source (Comp_Pragmas (J), Source_Control, Source_State);
         end if;

      end loop;

      Behind_Unit := False;

      --  Echo remaining lines
      declare
         End_Of_File : constant Cursor := File_Cursor (Kind => After_File);
      begin
         PP_Echo_Cursor_Range (Source_State.Echo_Cursor, End_Of_File);
      end;

      if Output_Mode /= Pipe and then
         Ada.Wide_Text_IO.Is_Open (Result_Out_File)
      then
         Ada.Wide_Text_IO.Close (Result_Out_File);

         if Out_File_Format /= Default then
            Correct_EOL;
         end if;
      end if;

      Set_Source_Status (SF, Processed);

      if Output_Mode in Replace .. Replace_No_Backup then

         if Hostparm.OpenVMS then
            Copy_File
              (Name     => Res_File_Name.all,
               Pathname => Source_Name (SF),
               Success  => Success,
               Mode     => Overwrite,
               Preserve => None);

         else
            Copy_File
              (Name     => Res_File_Name.all,
               Pathname => Source_Name (SF),
               Success  => Success,
               Mode     => Overwrite);
         end if;

         if not Success then
            Put (Standard_Error, "sparkify: can not write the reformatted ");
            Put (Standard_Error, "source into ");
            Put (Standard_Error, Source_Name (SF));
            New_Line (Standard_Error);

            Set_Source_Status (SF, Error_Detected);
         end if;
      end if;

   exception
      when Ex : Asis.Exceptions.ASIS_Inappropriate_Context          |
                Asis.Exceptions.ASIS_Inappropriate_Container        |
                Asis.Exceptions.ASIS_Inappropriate_Compilation_Unit |
                Asis.Exceptions.ASIS_Inappropriate_Element          |
                Asis.Exceptions.ASIS_Inappropriate_Line             |
                Asis.Exceptions.ASIS_Inappropriate_Line_Number      |
                Asis.Exceptions.ASIS_Failed                         =>

         Report_Unhandled_ASIS_Exception (Ex);

         if Output_Mode /= Pipe and then
            Ada.Wide_Text_IO.Is_Open (Result_Out_File)
         then
            Ada.Wide_Text_IO.Close (Result_Out_File);
         end if;

         Set_Source_Status (SF, Error_Detected);

      when Ex : others =>
         Report_Unhandled_Exception (Ex);

         if Output_Mode /= Pipe and then
            Ada.Wide_Text_IO.Is_Open (Result_Out_File)
         then
            Ada.Wide_Text_IO.Close (Result_Out_File);
         end if;

         Set_Source_Status (SF, Error_Detected);

   end Special_Print;

end Sparkify.Processing;
