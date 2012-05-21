------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                   G N A T 2 W H Y - D E C L S                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2012, AdaCore                   --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Atree;                use Atree;
with Einfo;                use Einfo;
with Sinfo;                use Sinfo;

with Alfa.Definition;      use Alfa.Definition;
with Alfa.Util;            use Alfa.Util;

with Why.Ids;              use Why.Ids;
with Why.Sinfo;            use Why.Sinfo;
with Why.Atree.Accessors;  use Why.Atree.Accessors;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Gen.Decl;         use Why.Gen.Decl;
with Why.Gen.Names;        use Why.Gen.Names;
with Why.Gen.Binders;      use Why.Gen.Binders;
with Why.Gen.Expr;         use Why.Gen.Expr;
with Why.Types;            use Why.Types;

with Gnat2Why.Expr;        use Gnat2Why.Expr;
with Gnat2Why.Nodes;       use Gnat2Why.Nodes;
with Gnat2Why.Types;       use Gnat2Why.Types;

with System.OS_Lib;
with Ada.Strings.Maps.Constants;
with Why.Atree.Mutators;        use Why.Atree.Mutators;
with Sem_Ch12;                  use Sem_Ch12;
with String_Utils;              use String_Utils;
with Namet;                     use Namet;
with Nlists;                    use Nlists;
with Sem_Util;                  use Sem_Util;
with Ada.Strings.Fixed;         use Ada.Strings.Fixed;
with Ada.Strings.Unbounded;     use Ada.Strings.Unbounded;
--  with Ada.Text_IO;
with Ada.Strings; use Ada.Strings;

package body Gnat2Why.Decls is

   ----------------
   -- Is_Mutable --
   ----------------

   function Is_Mutable (N : Node_Id) return Boolean
   is
   begin

      --  A variable is translated as mutable in Why if it is not constant on
      --  the Ada side, or if it is a loop parameter (of an actual loop, not a
      --  quantified expression.

      if Ekind (N) = E_Loop_Parameter then
         return not (Is_Quantified_Loop_Param (N));
      elsif Ekind (N) = E_Enumeration_Literal or else
        Is_Constant_Object (N) or else
        Ekind (N) in Named_Kind then
         return False;
      else
         return True;
      end if;
   end Is_Mutable;

   ------------------------
   -- Translate_Variable --
   ------------------------

   procedure Translate_Variable
     (File : in out Why_File;
      E     : Entity_Id)
   is
      Name : constant String := Full_Name (E);
      Decl : constant W_Declaration_Id :=
        (if In_Alfa (E) then
            New_Type
              (Name  => To_Ident (WNE_Type),
               Alias => +Why_Logic_Type_Of_Ada_Obj (E))
         else
            New_Type
              (Name => To_Ident (WNE_Type),
               Args => 0));
      Typ  : constant W_Primitive_Type_Id :=
               New_Abstract_Type (Name => Get_Name (W_Type_Id (Decl)));

   begin
      Open_Theory (File, Name);

      --  Generate an alias for the name of the object's type, based on the
      --  name of the object. This is useful when generating logic functions
      --  from Ada functions, to generate additional parameters for the global
      --  objects read.

      Emit (File.Cur_Theory, Decl);

      --  We generate a global ref

      Emit
        (File.Cur_Theory,
         New_Global_Ref_Declaration
           (Name     => To_Why_Id (E, Local => True),
            Labels   => (1 => New_Name_Label (E)),
            Ref_Type => Typ));

      Close_Theory (File, Filter_Entity => E);
   end Translate_Variable;

   ------------------------
   -- Translate_Constant --
   ------------------------

   procedure Translate_Constant
     (File   : in out Why_File;
      E      : Entity_Id)
   is
      Base_Name : constant String := Full_Name (E);
      Name      : constant String :=
                    (if Is_Full_View (E) then
                       Base_Name & "__full_view"
                     else
                       Base_Name);
      Typ  : constant W_Primitive_Type_Id := Why_Logic_Type_Of_Ada_Obj (E);
      Decl : constant Node_Id := Parent (E);
      Def  : W_Term_Id;

   begin
      --  Start with opening the theory to define, as the creation of a
      --  function for the logic term needs the current theory to insert an
      --  include declaration.

      Open_Theory (File, Name);

      --  Default values of parameters are not considered as the value of the
      --  constant representing the parameter.

      if Ekind (E) /= E_In_Parameter
        and then Present (Expression (Decl))
      then
         Def := Get_Pure_Logic_Term_If_Possible
           (File, Expression (Decl), Type_Of_Node (E));
      else
         Def := Why_Empty;
      end if;

      --  The definition of deferred constants is done in a separate theory, so
      --  that only code in the unit defining the deferred constant has access
      --  to its value. This allows supporting parameterized verification of
      --  client units not depending on the value of a delayed constant. This
      --  theory is added as a completion of the base theory defining the
      --  constant, so that further modules including the base theory also
      --  include the completion, for modules defined in this unit. Theories
      --  defined in other units only have access to the base theory. Note
      --  that modules in the same unit may also have access to the base
      --  theory only, if they are defined before this point.

      if Is_Full_View (E) then
         if Def = Why_Empty then
            Discard_Theory (File);

         else
            --  It may be the case that the full view has a more precise type
            --  than the partial view, for example when the type of the partial
            --  view is an indefinite array. In that case, convert back to the
            --  expected type for the constant.

            if Etype (Partial_View (E)) /= Etype (E) then
               Def := W_Term_Id (Insert_Conversion
                        (Domain   => EW_Term,
                         Ada_Node => Expression (Decl),
                         Expr     => W_Expr_Id (Def),
                         From     => Type_Of_Node (E),
                         To       => Type_Of_Node (Partial_View (E))));
            end if;

            Emit
              (File.Cur_Theory,
               New_Defining_Axiom
                 (Name        =>
                    To_Why_Id (E, Domain => EW_Term, Local => False),
                  Return_Type => Get_EW_Type (Typ),
                  Binders     => (1 .. 0 => <>),
                  Def         => Def));

            --  No filtering is necessary here, as the theory should on the
            --  contrary use the previously defined theory for the partial
            --  view. Attach the newly created theory as a completion of the
            --  existing one.

            Close_Theory (File, Filter_Entity => Empty);
            if In_Main_Unit_Body (E) then
               Add_Completion (Base_Name, Name, WF_Context_In_Body);
            else
               Add_Completion (Base_Name, Name, WF_Context_In_Spec);
            end if;
         end if;

      --  In the general case, we generate a "logic", with a defining axiom if
      --  necessary and possible.

      else
         Emit
           (File.Cur_Theory,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Why_Id (E, Domain => EW_Term, Local => True),
               Labels      => (1 => New_Name_Label (E)),
               Binders     => (1 .. 0 => <>),
               Return_Type => Typ));

         if Def /= Why_Empty then
            Emit
              (File.Cur_Theory,
               New_Defining_Axiom
                 (Name        =>
                    To_Why_Id (E, Domain => EW_Term, Local => True),
                  Return_Type => Get_EW_Type (Typ),
                  Binders     => (1 .. 0 => <>),
                  Def         => Def));
         end if;

         Close_Theory (File, Filter_Entity => E);
      end if;
   end Translate_Constant;

   ---------------------------------
   -- Translate_Container_Package --
   ---------------------------------

   procedure Translate_Container_Package
     (File_Type    : in out Why_File;
      File_Context : in out Why_File;
      E    : Entity_Id) is

      --  Replace each declaration's name by the appropriate name
      --  Generate a renaming of every type parameter module
      procedure Parse_Declarations
        (Decls          : List_Id;
         Assoc          : List_Id;
         Labs           : List_Id;
         Type_File_Name : String;
         Type_Source       : in out String_Access;
         Context_File_Name : String;
         Context_Source   : in out String_Access;
         Append : in out String_Access);

      --  Replace each formal parameter by the corresponding concrete parameter
      procedure Parse_Parameters
        (Assoc             :        List_Id;
         Labs              :        List_Id;
         Type_File_Name    :        String;
         Type_Source       : in out String_Access;
         Context_File_Name :        String;
         Context_Source    : in out String_Access);

      --  Use custom declaration to append Args to File.
      procedure Instantiate_Theory (Args : String_Access;
                                    File : in out Why_File);

      --  Copied from why_inter.adb
      function File_Base_Name_Of_Entity (E : Entity_Id) return String;

      --  Compute the name of a formal parameter
      function Get_Assoc_From_Param
        (CurAssoc : Node_Id;
         CurLabs  : Node_Id) return String;

      --  Generate arguments for renaming Assoc_Name by Theory_Name from
      --  File_Name in file My_File_Name
      procedure Make_Replacement
        (Assoc_Name   :        String;
         Theory_Name  :        String;
         Source       : in out String_Access;
         File_Name    :        String := "";
         My_File_Name :        String := "");

      procedure Make_Replacement
        (Assoc_Name   :        String;
         Theory_Name  :        String;
         Source       : in out String_Access;
         File_Name    :        String := "";
         My_File_Name :        String := "") is

         function Replace_All
           (Source  : String;
            Pattern : String;
            By      : String) return String;

         function Replace_All
           (Source  : String;
            Pattern : String;
            By      : String) return String is
            I : constant Natural := Index (Source, Pattern);
         begin
            if I = 0 then
               return Source;
            else
               return Replace_All
                 (Replace_Slice (Source, I, I + Pattern'Length - 1, By),
                  Pattern, By);
            end if;
         end Replace_All;
      begin
         --  Ada.Text_IO.Put (Assoc_Name);
         --  Ada.Text_IO.Put (" => ");
         if File_Name /= My_File_Name then
            Source := new String'(Replace_All
              (Source.all, Assoc_Name,
                 '"' & File_Name & '"' & "." & Theory_Name));
            --  Ada.Text_IO.Put_Line
            --    ('"' & File_Name & '"' & "." & Theory_Name);
         else
            Source := new String'(Replace_All
              (Source.all, Assoc_Name, Theory_Name));
            --  Ada.Text_IO.Put_Line (Theory_Name);
         end if;
      end Make_Replacement;

      function Get_Assoc_From_Param
        (CurAssoc : Node_Id;
         CurLabs  : Node_Id) return String is
         Potential_Assoc : constant Node_Id  :=
           Selector_Name (CurAssoc);
         --  Assoc is either association for the label if any or the label
         --  itself
         Assoc  : constant Node_Id  :=
           (if Present (Potential_Assoc) then Potential_Assoc
            else Defining_Identifier (CurLabs));
      begin
         Get_Unqualified_Name_String (Chars (Assoc));
         return Ada.Strings.Fixed.Translate
           (Name_Buffer (1 .. Name_Len),
            Ada.Strings.Maps.Constants.Lower_Case_Map);
      end Get_Assoc_From_Param;

      function File_Base_Name_Of_Entity (E : Entity_Id) return String is
         U : Node_Id;
      begin
         if Is_In_Standard_Package (E) then
            return Standard_Why_Package_Name;
         end if;
         U := Enclosing_Comp_Unit_Node (E);

         --  Itypes are not attached to the tree, so we go through the
         --  associated node

         if not Present (U) and then Is_Itype (E) then
            U := Enclosing_Comp_Unit_Node (Associated_Node_For_Itype (E));
         end if;

         --  Special handling for entities of subunits, we extract the library
         --  unit

         while Nkind (Unit (U)) = N_Subunit loop
            U := Library_Unit (U);
         end loop;
         return File_Name_Without_Suffix (Sloc (U));
      end File_Base_Name_Of_Entity;

      procedure Parse_Declarations
        (Decls             : List_Id;
         Assoc             : List_Id;
         Labs              : List_Id;
         Type_File_Name    : String;
         Type_Source       : in out String_Access;
         Context_File_Name : String;
         Context_Source   : in out String_Access;
         Append           : in out String_Access) is

         --  Generate a renaming of a type parameter module
         procedure Make_Parameter (Theory_Name : String;
                                   Assoc_Name  : String;
                                   File_Name   : String);

         --  Replace a declaration's name by the appropriate name
         procedure Parse_Declaration
           (Node    : Node_Id);

         procedure Make_Parameter (Theory_Name : String;
                                   Assoc_Name  : String;
                                   File_Name   : String) is

            CurAssoc : Node_Id := First (Assoc);
            CurLabs : Node_Id := First (Labs);
         begin
            --  Serch for Assoc_Name in the parameter list
            while Present (CurAssoc) loop
               declare
                  Current_Assoc : constant String :=
                    Get_Assoc_From_Param (CurAssoc, CurLabs);
                  Param : constant Node_Id :=
                    Explicit_Generic_Actual_Parameter (CurAssoc);
                  Assoc_Theory_Name : constant String :=
                    Capitalize_First (Full_Name (Entity (Param)));
                  Assoc_File_Name   : constant String :=
                    File_Base_Name_Of_Entity (Entity (Param)) &
                  Why_File_Suffix (Dispatch_Entity (Entity (Param)));
               begin
                  if Assoc_Name = Current_Assoc then
                     --  Generate a copy of the concrete parameter's module
                     --  Named Theory_Name
                     if File_Name = Assoc_File_Name then
                        Append :=
                          new String'("module "&Theory_Name&ASCII.LF&
                                      "use export module "&Assoc_Theory_Name&
                                      ASCII.LF&"end"&ASCII.LF&ASCII.LF&
                                      Append.all);
                     else
                        Append :=
                          new String'("module "&Theory_Name&ASCII.LF&
                                      "use export module "&'"'&
                                      Assoc_File_Name&'"'&
                                      "."&Assoc_Theory_Name&ASCII.LF&"end"&
                                      ASCII.LF&ASCII.LF&
                                      Append.all);
                     end if;
                     return;
                  end if;
                  Next (CurAssoc);
                  Next (CurLabs);
               end;
            end loop;
         end Make_Parameter;

         procedure Parse_Declaration
           (Node    : Node_Id) is
         begin
            case Nkind (Node) is
            when N_Subtype_Declaration | N_Private_Type_Declaration =>
               Get_Unqualified_Name_String
                 (Chars (Defining_Identifier (Node)));
               declare
                  Theory_Name : constant String := Capitalize_First
                    (Full_Name (Defining_Identifier (Node)));
                  Assoc_Name : constant String := Name_Buffer (1 .. Name_Len);
               begin
                  Make_Parameter (Theory_Name, Assoc_Name,
                                  Type_File_Name);
                  if not Comes_From_Source (Node) then
                     return;
                  end if;
                  Make_Replacement ("$$" & Assoc_Name, Theory_Name,
                                    Context_Source,
                                    Type_File_Name, Context_File_Name);
                  Make_Replacement ("$$" & Assoc_Name, Theory_Name,
                                    Type_Source);
                  Make_Replacement ("$" & Assoc_Name, Theory_Name,
                                    Context_Source);
                  Make_Replacement ("$" & Assoc_Name, Theory_Name,
                                    Type_Source);
               end;
            when N_Subprogram_Declaration
               | N_Subprogram_Renaming_Declaration =>
               if not Comes_From_Source (Node) then
                  return;
               end if;
               declare
                  Spec  : constant Node_Id := Specification (Node);
                  Theory_Name : constant String  :=
                    Capitalize_First (Get_Name_String (Chars
                      (Defining_Unit_Name (Spec))));

               begin

                  Get_Unqualified_Name_String
                    (Chars (Defining_Unit_Name (Spec)));
                  declare
                     Short_Name : constant String :=
                       Name_Buffer (1 .. Name_Len);
                     I : constant Natural :=
                       Ada.Strings.Fixed.Index (Theory_Name, Short_Name, 1);
                     Assoc_Name : constant String :=
                       Ada.Strings.Fixed.Translate
                         (Theory_Name (I .. Theory_Name'Length),
                          Ada.Strings.Maps.Constants.Lower_Case_Map);
                  begin
                     Make_Replacement ("$$" & Assoc_Name, Theory_Name,
                                       Context_Source);
                     Make_Replacement ("$" & Assoc_Name, Theory_Name,
                                       Context_Source);
                     Make_Replacement ("$$" & Assoc_Name, Theory_Name,
                                       Type_Source,
                                       Context_File_Name, Type_File_Name);
                     Make_Replacement ("$" & Assoc_Name, Theory_Name,
                                       Type_Source);
                  end;
               end;

            when N_Object_Declaration =>
               if not Comes_From_Source (Node) then
                  return;
               end if;
               Get_Unqualified_Name_String
                 (Chars (Defining_Identifier (Node)));
               declare
                  Theory_Name    : constant String  :=
                    Capitalize_First (Full_Name (Defining_Identifier (Node)));
                  Short_Name : constant String := Name_Buffer (1 .. Name_Len);
                  I : constant Natural :=
                    Ada.Strings.Fixed.Index (Theory_Name, Short_Name, 1);
                  Assoc_Name : constant String :=
                    Ada.Strings.Fixed.Translate
                      (Theory_Name (I .. Theory_Name'Length),
                       Ada.Strings.Maps.Constants.Lower_Case_Map);
               begin
                  Make_Replacement ("$$" & Assoc_Name, Theory_Name,
                                    Context_Source);
                  Make_Replacement ("$" & Assoc_Name, Theory_Name,
                                    Context_Source);
                  Make_Replacement ("$$" & Assoc_Name, Theory_Name,
                                    Type_Source,
                                    Context_File_Name, Type_File_Name);
                  Make_Replacement ("$" & Assoc_Name, Theory_Name,
                                    Type_Source);
               end;
            when others => null;
            end case;
         end Parse_Declaration;

         Cur : Node_Id := First (Decls);
      begin
         while Present (Cur) loop
            Parse_Declaration (Cur);
            Next (Cur);
         end loop;
      end Parse_Declarations;

      procedure Parse_Parameters
        (Assoc             :        List_Id;
         Labs              :        List_Id;
         Type_File_Name    : String;
         Type_Source       : in out String_Access;
         Context_File_Name : String;
         Context_Source    : in out String_Access) is

         CurAssoc : Node_Id;
         CurLabs  : Node_Id;
      begin
         CurAssoc := First (Assoc);
         CurLabs := First (Labs);
         while Present (CurAssoc) loop
            declare
               Param : constant Node_Id :=
                 Explicit_Generic_Actual_Parameter (CurAssoc);
               Assoc_Name : constant String :=
                 Get_Assoc_From_Param (CurAssoc, CurLabs);
               Assoc_Theory_Name : constant String :=
                 Capitalize_First (Full_Name (Entity (Param)));
               Assoc_File_Name   : constant String :=
                 File_Base_Name_Of_Entity (Entity (Param)) &
               Why_File_Suffix (Dispatch_Entity (Entity (Param)));
            begin
               Make_Replacement ("$$" & Assoc_Name, Assoc_Theory_Name,
                                 Type_Source,
                                 Assoc_File_Name, Type_File_Name);
               Make_Replacement ("$$" & Assoc_Name, Assoc_Theory_Name,
                                 Context_Source,
                                 Assoc_File_Name, Context_File_Name);
               Make_Replacement ("$" & Assoc_Name, Assoc_Theory_Name,
                                 Type_Source);
               Make_Replacement ("$" & Assoc_Name, Assoc_Theory_Name,
                                 Context_Source);
            end;
            Next (CurAssoc);
            Next (CurLabs);
         end loop;
      end Parse_Parameters;

      procedure Instantiate_Theory (Args : String_Access;
                                    File : in out Why_File) is
         F : Natural;
         S : constant String := Args.all;
         Max : constant Natural := 2**15;
         Cut : Natural := 0;
      begin
         while S'Length - Cut >= Max loop
            F := Cut;
            Cut := Index (Source => S,
                          Pattern => " ",
                          From => Cut + Max - 1,
                          Going => Backward);
            File_Append_To_Theories
              (File.File,
               Why.Atree.Builders.New_Custom_Declaration
                 (Domain => EW_Prog,
                  Content => New_Identifier
                    (Name => S (F + 1 .. Cut))));
         end loop;
         File_Append_To_Theories
           (File.File,
            Why.Atree.Builders.New_Custom_Declaration
              (Domain => EW_Prog,
               Content => New_Identifier (Name => S (Cut + 1 .. S'Length))));
      end Instantiate_Theory;

      function Read_File (File_Name : String) return String;

      function Read_File (File_Name : String) return String is
         FD : constant System.OS_Lib.File_Descriptor :=
           System.OS_Lib.Open_Read (File_Name, System.OS_Lib.Text);
         L : constant Natural := Natural (System.OS_Lib.File_Length (FD));
         S : String := (1 .. L => <>);
         Ret : Natural;
      begin
         Ret := System.OS_Lib.Read (FD, S'Address, L);
         if Ret /= L then
            raise Program_Error;
         end if;
         System.OS_Lib.Close (FD);
         return S;
      end Read_File;

      Decls : constant List_Id := Visible_Declarations (Parent (E));
      UName : constant String := Full_Name (E);
      Generic_Name : constant String := Get_Name_String
        (Chars (Generic_Parent (Parent (E))));
      Assoc : constant List_Id := Generic_Associations
        (Get_Package_Instantiation_Node (E));
      --  use Parent field to reach N_Genereic_Package_Declaration
      Labs : constant List_Id := Generic_Formal_Declarations (Parent (Parent
        (Parent (Generic_Parent (Parent (E))))));
      Type_File_Name : constant String := File_Type.Name.all;
      Type_Source : String_Access := new String'
        (Read_File ("../"&Generic_Name & "_types.mlw"));
      Context_File_Name : constant String := File_Context.Name.all;
      Context_Source : String_Access := new String'
        (Read_File ("../"&Generic_Name & "_main.mlw"));
      Append : String_Access := new String'("");
   begin
      --  Ada.Text_IO.Put_Line ("---------------------------");
      Parse_Parameters (Assoc, Labs, Type_File_Name, Type_Source,
                        Context_File_Name, Context_Source);
      Parse_Declarations (Decls, Assoc, Labs, Type_File_Name, Type_Source,
                          Context_File_Name, Context_Source, Append);
      File_Append_To_Theories
        (File_Type.File,
         Why.Atree.Builders.New_Custom_Declaration
           (Domain => EW_Prog,
            Content => New_Identifier (Name => Append.all)));
      Make_Replacement ("$Types", "Types_"&UName,
                        Type_Source);
      Make_Replacement ("$Main", "Main_"&UName,
                        Context_Source);
      Instantiate_Theory (Type_Source, File_Type);
      --  Ada.Text_IO.Put_Line ("----------- THEORY -----------");
      Instantiate_Theory (Context_Source, File_Context);
      --  Ada.Text_IO.Put_Line ("----------- CONTEXT ----------");
   end Translate_Container_Package;

end Gnat2Why.Decls;
