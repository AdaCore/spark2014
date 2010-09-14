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

with Ada.Containers.Vectors;           use Ada.Containers;
with Ada.Strings.Wide_Unbounded;       use Ada.Strings.Wide_Unbounded;
with Ada.Text_IO;                      use Ada.Text_IO;
with Ada.Wide_Text_IO;

with GNAT.OS_Lib;                      use GNAT.OS_Lib;
with Hostparm;

with Asis;                             use Asis;
with Asis.Compilation_Units;           use Asis.Compilation_Units;
with Asis.Elements;                    use Asis.Elements;
with Asis.Exceptions;
with Asis.Text;                        use Asis.Text;
with Asis.Clauses;                     use Asis.Clauses;
with Asis.Declarations;                use Asis.Declarations;
with Asis.Extensions.Flat_Kinds;       use Asis.Extensions.Flat_Kinds;
with Asis.Set_Get;                     use Asis.Set_Get;

with ASIS_UL.Output;                   use ASIS_UL.Output;
with ASIS_UL.Global_State.CG.Sparkify;

with Sparkify.Basic;                   use Sparkify.Basic;
with Sparkify.Common;                  use Sparkify.Common;
with Sparkify.Names;                   use Sparkify.Names;
with Sparkify.Options;                 use Sparkify.Options;
with Sparkify.Output;                  use Sparkify.Output;
with Sparkify.PP_Output;               use Sparkify.PP_Output;
with Sparkify.Source_Traversal;        use Sparkify.Source_Traversal;
with Sparkify.State;                   use Sparkify.State;
with Sparkify.Cursors;                 use Sparkify.Cursors;
with Sparkify.Pre_Operations;
with Sparkify.Stringset;

package body Sparkify.Processing is

   ----------------
   -- Print_Decl --
   ----------------

   procedure Print_Decl (Element : Asis.Declaration);

   procedure Print_Decl (Element : Asis.Declaration) is
      Full_Span      : constant Asis.Text.Span := Compilation_Span (Element);

      procedure Print_Decl_List (Decl_Items : Asis.Declarative_Item_List);

      procedure Print_Decl_List (Decl_Items : Asis.Declarative_Item_List) is
      begin
         --  Traverse library item (or subunit) itself
         for J in Decl_Items'Range loop
            Pre_Operations.Traverse_Element_And_Print (Decl_Items (J));
         end loop;
      end Print_Decl_List;
   begin
      --  Feeding the line table
      Lines_Table.Set_Last (Full_Span.Last_Line);
      Lines_Table.Table (1 .. Full_Span.Last_Line) :=
         Lines_Table.Table_Type
           (Lines (Element    => Element,
                   First_Line => Full_Span.First_Line,
                   Last_Line  => Full_Span.Last_Line));

      The_Last_Line   := Full_Span.Last_Line;
      The_Last_Column := Full_Span.Last_Column;

      case Declaration_Kind (Element) is
         when A_Package_Declaration |
              A_Generic_Package_Declaration =>
            declare
               Private_Items : constant Declarative_Item_List :=
                                 Private_Part_Declarative_Items
                                   (Declaration     => Element,
                                    Include_Pragmas => False);
               Visible_Items : constant Declarative_Item_List :=
                                 Visible_Part_Declarative_Items
                                   (Declaration     => Element,
                                    Include_Pragmas => False);
               Decl_Items    : constant Declarative_Item_List :=
                                 Visible_Items & Private_Items;
            begin
               if Declaration_Kind (Element) = A_Package_Declaration then
                  Print_Decl_List (Decl_Items);
               else
                  declare
                     Formal_Items : constant Element_List :=
                                      Generic_Formal_Part
                                        (Declaration     => Element,
                                         Include_Pragmas => False);
                  begin
                     Print_Decl_List (Formal_Items & Decl_Items);
                  end;
               end if;
            end;
         when A_Package_Body_Declaration =>
            declare
               Decl_Items : constant Declarative_Item_List :=
                              Body_Declarative_Items
                                (Declaration     => Element,
                                 Include_Pragmas => False);
            begin
               Print_Decl_List (Decl_Items);
            end;
         when others =>
            Print_Decl_List ((1 => Element));
      end case;
   end Print_Decl;

   -------------------
   -- Special_Print --
   -------------------

   procedure Special_Print (Unit : Asis.Compilation_Unit; SF : SF_Id) is
      Unit_Decl          : constant Asis.Declaration :=
                             Unit_Declaration (Unit);
      Match_Unit         : constant Asis.Compilation_Unit :=
                             Corresponding_Body (Unit);
      Unit_Body          : constant Asis.Declaration :=
                             (if Is_Nil (Match_Unit) then Nil_Element
                              else Unit_Declaration (Match_Unit));
      Is_Decl_With_Body  : constant Boolean :=
                             not Is_Nil (Match_Unit)
                               and then not Is_Nil (Unit_Body)
                               and then not Is_Equal (Match_Unit, Unit);

      Context_Clause     : constant Asis.Context_Clause_List :=
                             Context_Clause_Elements (Unit, True);
      Comp_Pragmas       : constant Asis.Element_List :=
                             Compilation_Pragmas (Unit);
      First_Pragma_After : Asis.List_Index := Comp_Pragmas'Last + 1;

      Full_Span          : constant Asis.Text.Span :=
                             Compilation_Span (Unit_Decl);
      Unit_Span          : constant Asis.Text.Span :=
                             Element_Span (Unit_Decl);

      Source_Control     : Asis.Traverse_Control := Asis.Continue;
      Source_State       : Source_Traversal_State;

      Unit_Name          : constant Wide_String :=
                             Flat_Package_Name
                               (Declaration_Unique_Name (Unit_Decl));

      Success            : Boolean := False;
   begin
      Sparkify.State.Initialize;
      Sparkify.Names.Initialize;

      --  Feeding the line table

      Lines_Table.Set_Last (Full_Span.Last_Line);

      Lines_Table.Table (1 .. Full_Span.Last_Line) :=
         Lines_Table.Table_Type
           (Lines (Element    => Unit_Decl,
                   First_Line => Full_Span.First_Line,
                   Last_Line  => Full_Span.Last_Line));

      --  To keep the reference to the current unit in a global variable
      The_Unit := Unit;

      --  Set after The_Unit has been set
      Source_State := Initial_State;

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

      if Source_State.Phase = Printing_Spec then
         --  Currently processing a package declaration. Get the packages
         --  with'ed in its declaration and its body to generate
         --  a corresponding SPARK inherit clause.
         declare
            Packages : Nameset.Set := Nameset.Empty_Set;

            procedure Print_Inherited_Packages
              (Clauses : Asis.Context_Clause_List);

            procedure Print_Inherited_Packages
              (Clauses : Asis.Context_Clause_List) is
            begin
               for J in Clauses'Range loop
                  declare
                     Clause : constant Asis.Element := Clauses (J);
                  begin
                     if Clause_Kind (Clause) = A_With_Clause then
                        declare
                           Names : constant Asis.Name_List :=
                                     Clause_Names (Clause);
                        begin
                           for Name_Idx in Names'Range loop
                              declare
                                 Pack_Name : constant Wide_String :=
                                    Flat_Package_Name
                                      (Element_Name (Names (Name_Idx)));
                              begin
                                 Nameset.Include
                                   (Packages, Normalized_Name (Pack_Name));
                                 if Current_Pass = Printing_Internal then
                                    Nameset.Include
                                      (Packages, Normalized_Name
                                         (External_Prefix & Pack_Name));
                                 end if;
                              end;
                           end loop;
                        end;
                     end if;
                  end;
               end loop;
            end Print_Inherited_Packages;

         begin
            if Current_Pass = Printing_External
              or else Current_Pass = Printing_Internal then
               --  The external and internal packages have a with-clause on
               --  the data one
               PP_Word ("with " & Unit_Name & ";");
               --  Add all possible use-type clauses in SPARK code, to make for
               --  the absence of a use-package clauses.
               Sparkify.Pre_Operations.Print_All_Use_Type (Unit_Decl);
               if not Is_Nil (Unit_Body) then
                  Sparkify.Pre_Operations.Print_All_Use_Type (Unit_Body);
               end if;
               --  Always inherit the data package in an external or internal
               --  package
               Nameset.Include (Packages, Normalized_Name (Unit_Name));
            end if;

            if Current_Pass = Printing_Internal then
               --  The internal package has a with-clause on the external one
               PP_Word ("with " & External_Prefix & Unit_Name & ";");
               --  Always inherit the external package in an internal package
               Nameset.Include (Packages,
                                Normalized_Name (External_Prefix & Unit_Name));
            end if;

            if Is_Decl_With_Body and then
              Current_Pass in Printing_Subprograms then
               declare
                  Body_Clauses : constant Asis.Context_Clause_List :=
                                   Context_Clause_Elements (Match_Unit, True);
               begin
                  Print_Inherited_Packages (Context_Clause & Body_Clauses);
               end;
            else
               Print_Inherited_Packages (Context_Clause);
            end if;

            --  Always with and inherit the parent package in a child package
            declare
               Encl_Unit : constant Asis.Compilation_Unit :=
                                Corresponding_Parent_Declaration (Unit);
            begin
               if not (Is_Nil (Encl_Unit) or Is_Standard (Encl_Unit)) then
                  declare
                     Encl_Element : constant Asis.Declaration :=
                                      Unit_Declaration (Encl_Unit);
                     Parent_Name  : constant Wide_String :=
                                      Declaration_Unique_Name (Encl_Element);
                  begin
                     PP_Word ("with " & Parent_Name & ";");
                     Nameset.Include (Packages, Normalized_Name (Parent_Name));
                  end;
               end if;
            end;

            declare
               Packages_Text : constant Wide_String :=
                 Concat_Names (Packages, ", ");
               Line : constant Line_Number_Positive :=
                 Line_Number_Positive'Max (First_Line_Number (Unit_Decl), 2)
                 - 1;
            begin
               if Packages_Text /= "" then
                  PP_Echo_Cursor_Range (Source_State.Echo_Cursor,
                                        Cursor_Before (Unit_Decl));
                  PP_Inherit (Line,
                              Element_Span (Unit_Decl).First_Column,
                              Packages_Text);
                  Source_State.Echo_Cursor := Cursor_At (Unit_Decl);
               end if;
            end;
         end;
      end if;

      --  Step #3: Library item (or subunit) itself

      In_Context_Clause := False;
      In_Unit           := True;

      if (Current_Pass = Printing_Data
          or else Current_Pass = Printing_External)
        and then Source_State.Phase = Printing_Spec then
         declare
            package Element_Container is new
              Vectors (Positive, Asis.Element, Is_Equal);

            --  Collect the names of declarations Decl
            function Names_Of_Declarations
              (Decls : Element_Container.Vector) return Stringset.Set;

            function Names_Of_Declarations
              (Decls : Element_Container.Vector) return Stringset.Set
            is
               Names : Stringset.Set;
               Decl  : Element_Container.Cursor :=
                         Element_Container.First (Decls);
            begin
               while Element_Container.Has_Element (Decl) loop
                  declare
                     Decl_Names : constant Defining_Name_List :=
                                    Asis.Declarations.Names
                                      (Element_Container.Element (Decl));
                  begin
                     for K in 1 .. Decl_Names'Length loop
                        declare
                           Name_Str : constant Unbounded_Wide_String :=
                                        To_Unbounded_Wide_String
                                          (Defining_Name_Image
                                             (Decl_Names (K)));
                        begin
                           Stringset.Insert
                             (Container => Names, New_Item  => Name_Str);
                        end;
                     end loop;
                  end;
                  Element_Container.Next (Decl);
               end loop;

               return Names;
            end Names_Of_Declarations;

            --  Concatenate the names of Names separated by Sep
            function Concat_Names
              (Names : Stringset.Set;
               Sep   : Wide_String) return Unbounded_Wide_String;

            function Concat_Names
              (Names : Stringset.Set;
               Sep   : Wide_String) return Unbounded_Wide_String
            is
               Name   : Stringset.Cursor := Stringset.First (Names);
               Concat : Unbounded_Wide_String;
            begin
               --  First take into account the first name
               if Stringset.Has_Element (Name) then
                  Concat := Stringset.Element (Name);
                  Stringset.Next (Name);
               end if;

               --  Then concatenate all remaining names
               while Stringset.Has_Element (Name) loop
                  Concat := Concat & Sep & Stringset.Element (Name);
                  Stringset.Next (Name);
               end loop;

               return Concat;
            end Concat_Names;

            Private_Items  : constant Declarative_Item_List :=
                              Private_Part_Declarative_Items
                                (Declaration     => Unit_Decl,
                                 Include_Pragmas => False);
            Visible_Items  : constant Declarative_Item_List :=
                              Visible_Part_Declarative_Items
                                (Declaration     => Unit_Decl,
                                 Include_Pragmas => False);
            Decl_Items     : constant Declarative_Item_List :=
                              Private_Items & Visible_Items;

            Items          : Element_Container.Vector;

            Body_Decl      : constant Asis.Declaration :=
                              Corresponding_Body (Unit_Decl);

            Column_Start   : constant Character_Position_Positive :=
                              Element_Span (Unit_Decl).First_Column;

            Pack_Names     : constant Defining_Name_List :=
                              Asis.Declarations.Names (Unit_Decl);

            Item           : Element_Container.Cursor;
            Own_Items      : Element_Container.Vector;
            Own_Str        : Unbounded_Wide_String;
            Init_Str       : Unbounded_Wide_String;
            Own_Set        : Stringset.Set;

            This_Unit_Name : Unbounded_Wide_String;
         begin
            if Current_Pass = Printing_Data then
               This_Unit_Name := To_Unbounded_Wide_String (Unit_Name);
            else
               pragma Assert (Current_Pass = Printing_External);
               This_Unit_Name :=
                 To_Unbounded_Wide_String (External_Prefix & Unit_Name);
            end if;

            --  First collect all declarations in both the package declaration
            --  and the package body in Items

            for J in Decl_Items'Range loop
               Element_Container.Append (Items, Decl_Items (J));
            end loop;

            if Declaration_Kind (Unit_Decl) =
              A_Generic_Package_Declaration
            then
               declare
                  Formal_Items : constant Element_List :=
                                   Generic_Formal_Part
                                     (Declaration     => Unit_Decl,
                                      Include_Pragmas => False);
               begin
                  for J in Formal_Items'Range loop
                     Element_Container.Append (Items, Formal_Items (J));
                  end loop;
               end;
            end if;

            if not Is_Nil (Body_Decl) then
               declare
                  Body_Items : constant Declarative_Item_List :=
                                 Body_Declarative_Items
                                   (Declaration     => Body_Decl,
                                    Include_Pragmas => False);
               begin
                  for J in Body_Items'Range loop
                     Element_Container.Append (Items, Body_Items (J));
                  end loop;
               end;
            end if;

            --  Then filter those declarations which correspond to global
            --  variables and print them as own (and initializes when
            --  appropriate) variables in SPARK

            Item := Element_Container.First (Items);

            while Element_Container.Has_Element (Item) loop
               declare
                  El : constant Asis.Element :=
                         Element_Container.Element (Item);
               begin

                  --  Add all global variable declarations as "own" variables
                  if Flat_Element_Kind (El) = A_Variable_Declaration or else
                    Flat_Element_Kind (El) = A_Formal_Object_Declaration
                  then
                     Element_Container.Append (Own_Items, El);
                  end if;

               end;
               Element_Container.Next (Item);
            end loop;

            --  Get strings corresponding to lists of names of global variables
            Own_Set := Names_Of_Declarations (Own_Items);
            Own_Str := Concat_Names (Own_Set, ", ");

            --  If the global variable is initialized at declaration, or if the
            --  package body statement writes (initializes) it, it will be
            --  counted in the writes effects of this package.
            --  TODO: do something special for global variables not from this
            --  package which are written in the package body statement
            Init_Str :=
              ASIS_UL.Global_State.CG.Sparkify.All_Global_Writes
                (Unit_Decl, ", ", Own_Set);

            pragma Assert (Pack_Names'Length = 1);

            PP_Word ("package " & To_Wide_String (This_Unit_Name));

            if Current_Pass = Printing_Data then
               --  Print the package state annotations
               PP_Package_State (Column      => Column_Start,
                                 Own         => To_Wide_String (Own_Str),
                                 Initializes => To_Wide_String (Init_Str));
            end if;

            PP_Word_Alone_On_Line ("is");

            if Current_Pass = Printing_Data then
               PP_Word ("pragma Elaborate_Body ("
                         & To_Wide_String (This_Unit_Name) & ");");
            end if;

            Print_Decl (Unit_Decl);
            if Is_Decl_With_Body then
               Print_Decl (Unit_Body);
            end if;
            PP_Word_Alone_On_Line ("end " &
                                   To_Wide_String (This_Unit_Name) & ";");
         end;
      else
         Traverse_Source (Unit_Decl, Source_Control, Source_State);

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

            if Is_Equal
                 (Enclosing_Compilation_Unit (Comp_Pragmas (J)), Unit) then
               --  We may have configuration pragmas in the list
               Traverse_Source
                 (Comp_Pragmas (J), Source_Control, Source_State);
            end if;

         end loop;

         Behind_Unit := False;

         --  Echo remaining lines
         declare
            End_Of_File : constant Cursor := File_Cursor (Kind => After_File);
         begin
            PP_Echo_Cursor_Range (Source_State.Echo_Cursor, End_Of_File);
         end;
      end if;

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
