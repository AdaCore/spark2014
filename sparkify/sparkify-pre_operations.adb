------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--               S P A R K I F Y . P R E _ O P E R A T I O N S              --
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
with Ada.Strings.Wide_Fixed;           use Ada.Strings.Wide_Fixed;

with Asis.Compilation_Units;           use Asis.Compilation_Units;
with Asis.Definitions;                 use Asis.Definitions;
with Asis.Extensions;                  use Asis.Extensions;
with Asis.Text;                        use Asis.Text;
with Asis.Elements;                    use Asis.Elements;
with Asis.Expressions;                 use Asis.Expressions;
with Asis.Declarations;                use Asis.Declarations;
with Asis.Statements;                  use Asis.Statements;
with Asis.Set_Get;                     use Asis.Set_Get;

with ASIS_UL.Output;                   use ASIS_UL.Output;
with ASIS_UL.Strings;                  use ASIS_UL.Strings;
with ASIS_UL.Global_State.CG.Sparkify;

with Sparkify.PP_Output;               use Sparkify.PP_Output;
with Sparkify.Names;                   use Sparkify.Names;
with Sparkify.Source_Line_Buffer;      use Sparkify.Source_Line_Buffer;
with Sparkify.Cursors;                 use Sparkify.Cursors;
with Sparkify.Basic;                   use Sparkify.Basic;
with Sparkify.Source_Traversal;        use Sparkify.Source_Traversal;
with Ada.Strings.Wide_Unbounded;       use Ada.Strings.Wide_Unbounded;

package body Sparkify.Pre_Operations is

   -----------------------
   -- Local subprograms --
   -----------------------

   function Argument_By_Name_And_Position
     (Args     : Asis.Association_List;
      Name     : Name_String;
      Position : Natural)
      return     Asis.Association;
   pragma Precondition (Args'Length > Position);
   --  Return the argument with name Name and position Position from the list
   --  of arguments Args

   function Has_SPARK_Contract (Pragmas : Pragma_Element_List) return Boolean;
   --  Detects whether the list of pragmas Pragmas defines a SPARK contract

   procedure SPARK_Contract
     (Pragmas     : Pragma_Element_List;
      Is_Function : Boolean;
      Column      : Character_Position_Positive);
   --  Print preconditions and postconditions in SPARK syntax

   procedure SPARK_Data_Flow
     (Element     : Asis.Element;
      Is_Function : Boolean;
      Column      : Character_Position_Positive);
   --  Print data flow contracts in SPARK syntax

   procedure Traverse_Element_And_Print (Element : Asis.Element);
   --  Traverse Element in Printing_Code mode (prefixing identifiers et cetera)

   procedure Reach_Element_And_Traverse
     (Element : Asis.Element;
      State   : in out Source_Traversal_State);
   --  Echo everything before Element; then, call Traverse_Element_And_Print
   --  to set prefixing identifiers mode At the end of procedure,
   --  the cursor is set after Element.

   function Is_Defined_In_Standard_Or_Current_Compilation_Unit
     (Element : Asis.Element) return Boolean;

   function Prepend_Package_Name
     (Element : Asis.Element;
      Name    : Wide_String) return Wide_String;
   --  Functions would be call by an An_Identifier_Pre_Op or others
   --  Methodes where an Identifier should be prefixed by its package name

   function Simple_Subtype_Indication
     (Element : Subtype_Indication) return Boolean;
   --  Return True if the subtype indication is a simple subtype mark

   function Transform_Subtype_Indication
     (Element      : Subtype_Indication;
      Column_Start : Character_Position_Positive) return Wide_String;
   --  Return the subtype indication's identifier or create new subtype name

   function Transform_A_Discrete_Range
     (Element       : Asis.Discrete_Range;
      Column_Start  : Character_Position_Positive;
      For_Loop_Mode : Boolean := False) return Wide_String;

   function Transform_An_Index_Constraint
     (Element      : Asis.Constraint;
      Column_Start : Character_Position_Positive) return Wide_String;

   function Transform_Constrained_Array_Definition
     (Element      :        Asis.Type_Definition;
      Column_Start : Character_Position_Positive) return Wide_String;

   -----------------------------
   -- A_Loop_Statement_Pre_Op --
   -----------------------------

   procedure A_Loop_Statement_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);

      function Has_Iteration_Scheme
        (Loop_Element : Asis.Element)
        return Boolean;
      --  Return True if the loop statement has an iteration scheme
      --  (i.e. is either a for loop or a while loop).

      function Get_Iteration_Scheme
        (Loop_Element : Asis.Element)
        return Asis.Element;
      pragma Precondition (Has_Iteration_Scheme (Loop_Element));
      --  Return this loop's iteration scheme.

      --------------------------
      -- Has_Iteration_Scheme --
      --------------------------

      function Has_Iteration_Scheme
        (Loop_Element : Asis.Element)
        return Boolean is
      begin
         return Flat_Element_Kind (Loop_Element) = A_For_Loop_Statement
           or else Flat_Element_Kind (Loop_Element) = A_While_Loop_Statement;
      end Has_Iteration_Scheme;

      --------------------------
      -- Get_Iteration_Scheme --
      --------------------------

      function Get_Iteration_Scheme
        (Loop_Element : Asis.Element)
        return Asis.Element is
      begin
         if Flat_Element_Kind (Loop_Element) = A_For_Loop_Statement then
            return For_Loop_Parameter_Specification (Loop_Element);
         else
            return While_Condition (Loop_Element);
         end if;
      end Get_Iteration_Scheme;

      Statements        : constant Element_List :=
                            Loop_Statements (Element, Include_Pragmas => True);
      Last_Pragma_Index : Integer := Statements'First - 1;
   begin

      for Index in Statements'Range loop
         declare
            Elt : constant Asis.Element := Statements (Index);
         begin
            if Element_Kind (Elt) /= A_Pragma then
               Last_Pragma_Index := Index - 1;
               exit;
            end if;
         end;
      end loop;

      if Has_Iteration_Scheme (Element) then
         declare
            Iter_Scheme  : constant Asis.Element :=
                             Get_Iteration_Scheme (Element);
            Column_Start : constant Character_Position_Positive :=
                             Element_Span (Element).First_Column;
         begin
            PP_Echo_Cursor_Range
              (State.Echo_Cursor, Cursor_Before (Element));
            State.Echo_Cursor := Cursor_At (Element);

            if Flat_Element_Kind (Element) = A_For_Loop_Statement then
               declare
                  Discrete_Range : constant Asis.Discrete_Range :=
                                     Specification_Subtype_Definition
                                       (Iter_Scheme);
                  Subtype_Str    : constant Wide_String :=
                                     Transform_A_Discrete_Range
                                       (Discrete_Range, Column_Start,
                                        For_Loop_Mode => True);
               begin
                  PP_Echo_Cursor_Range
                    (State.Echo_Cursor, Cursor_Before (Discrete_Range));
                  State.Echo_Cursor := Cursor_At (Discrete_Range);
                  PP_Word (Subtype_Str);
                  Reach_Element_And_Traverse (Discrete_Range, State);
               end;
            else
               --  The iteration scheme can contain identifiers;
               --  they should be prefixed if needed. To do so,
               --  we should doTraverse_Source on what's before
               --  the first statement.
               Reach_Element_And_Traverse (Iter_Scheme, State);
            end if;
         end;
      end if;

      if Statements'First <= Last_Pragma_Index then
         declare
            Pragmas      : constant Pragma_Element_List :=
                            Statements (Statements'First .. Last_Pragma_Index);
            Inv_Exprs    : Expression_List (1 .. Pragmas'Length);
            Inv_Count    : Natural := 0;
            Column_Start : constant Character_Position_Positive :=
                             Element_Span
                               (Pragmas (Pragmas'First)).First_Column;
         begin
            PP_Echo_Cursor_Range
              (State.Echo_Cursor, Cursor_Before (Pragmas (Pragmas'First)));

            for Index in Pragmas'Range loop
               if Pragma_Kind (Pragmas (Index)) = An_Assert_Pragma then
                  declare
                     Element : constant Pragma_Element := Pragmas (Index);
                     Args    : constant Association_List :=
                                 Pragma_Argument_Associations (Element);
                     Arg     : constant Association :=
                                 Argument_By_Name_And_Position
                                   (Args,
                                    Nil_Name,
                                    Check_Position_In_Assert);
                     Expr    : constant Asis.Expression :=
                                Actual_Parameter (Arg);
                  begin
                     Inv_Count := Inv_Count + 1;
                     Inv_Exprs (Inv_Count) := Expr;
                  end;
               end if;
            end loop;

            if Inv_Count /= 0 then
               PP_Assert (Column_Start, Inv_Exprs (1 .. Inv_Count));
            end if;

            State.Echo_Cursor := Cursor_After (Pragmas (Pragmas'Last));
         end;

      else
         declare
            Elt : constant Asis.Element := Statements (Statements'First);
         begin
            PP_Echo_Cursor_Range
              (State.Echo_Cursor, Cursor_Before (Elt));
            PP_Assert (First_Line_Number (Elt),
                       Element_Span (Elt).First_Column,
                       "True");
            State.Echo_Cursor := Cursor_Before (Elt);
         end;
         SLOC_Warning ("implicit loop invariant",
                       Build_GNAT_Location (Element));
      end if;

   end A_Loop_Statement_Pre_Op;

   ----------------------------------
   -- A_Package_Declaration_Pre_Op --
   ----------------------------------

   procedure A_Package_Declaration_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);

      package Element_Container is new
        Vectors (Positive, Asis.Element, Is_Equal);

      --  Concatenate the names of declarations Decl separated by Sep
      function Names_Of_Declarations
        (Decls : Element_Container.Vector;
         Sep   : Wide_String) return Unbounded_Wide_String;

      function Names_Of_Declarations
        (Decls : Element_Container.Vector;
         Sep   : Wide_String) return Unbounded_Wide_String
      is
         Names : Unbounded_Wide_String;
         Decl  : Element_Container.Cursor := Element_Container.First (Decls);
      begin

         --  First take into account the first global variable
         if Element_Container.Has_Element (Decl) then
            declare
               Decl_Names : constant Defining_Name_List :=
                 Asis.Declarations.Names (Element_Container.Element (Decl));
            begin
               pragma Assert (Decl_Names'Length > 0);
               Names := To_Unbounded_Wide_String
                 (Defining_Name_Image (Decl_Names (1)));
               for K in 2 .. Decl_Names'Length loop
                  Names := Names & Sep & Defining_Name_Image (Decl_Names (K));
               end loop;
               Element_Container.Next (Decl);
            end;
         end if;

         --  Then concatenate all remaining global variables
         while Element_Container.Has_Element (Decl) loop
            declare
               Decl_Names : constant Defining_Name_List :=
                 Asis.Declarations.Names (Element_Container.Element (Decl));
            begin
               for K in 1 .. Decl_Names'Length loop
                  Names := Names & Sep & Defining_Name_Image (Decl_Names (K));
               end loop;
            end;
            Element_Container.Next (Decl);
         end loop;

         return Names;

      end Names_Of_Declarations;

      Private_Items : constant Declarative_Item_List :=
        Private_Part_Declarative_Items (Declaration     => Element,
                                        Include_Pragmas => False);
      Visible_Items : constant Declarative_Item_List :=
        Visible_Part_Declarative_Items (Declaration     => Element,
                                        Include_Pragmas => False);
      Decl_Items : constant Declarative_Item_List :=
        Private_Items & Visible_Items;

      Items : Element_Container.Vector;

      Body_Decl : constant Asis.Declaration := Corresponding_Body (Element);

      Column_Start : constant Character_Position_Positive :=
        Element_Span (Element).First_Column;
   begin

      --  First collect all declarations in both the package declaration and
      --  the package body in Items

      for J in Decl_Items'Range loop
         Element_Container.Append (Items, Decl_Items (J));
      end loop;

      if not Is_Nil (Body_Decl) then
         declare
            Body_Items : constant Declarative_Item_List :=
              Body_Declarative_Items (Declaration     => Body_Decl,
                                      Include_Pragmas => False);
         begin
            for J in Body_Items'Range loop
               Element_Container.Append (Items, Body_Items (J));
            end loop;
         end;
      end if;

      --  Then filter those declarations which correspond to global variables
      --  and print them as own (and initializes when appropriate) variables
      --  in SPARK

      declare
         Item : Element_Container.Cursor := Element_Container.First (Items);
         Own_Items         : Element_Container.Vector;
         Own_Str, Init_Str : Unbounded_Wide_String;

         Current_Cursor : Cursor;
         Pack_Names  : constant Defining_Name_List :=
           Asis.Declarations.Names (Element);
      begin
         while Element_Container.Has_Element (Item) loop
            declare
               El : constant Asis.Element := Element_Container.Element (Item);
            begin

               --  Add all global variable declarations as "own" variables
               if Flat_Element_Kind (El) = A_Variable_Declaration then
                  Element_Container.Append (Own_Items, El);
               end if;

            end;
            Element_Container.Next (Item);
         end loop;

         --  Get strings corresponding to lists of names of global variables
         Own_Str  := Names_Of_Declarations (Own_Items, ", ");

         --  If the global variable is initialized at declaration, or if the
         --  package body statement writes (initializes) it, it will be counted
         --  in the writes effects of this package.
         --  TODO: do something special for global variables not from this
         --  package which are written in the package body statement
         Init_Str :=
           ASIS_UL.Global_State.CG.Sparkify.All_Global_Writes (Element, ", ");

         pragma Assert (Pack_Names'Length = 1);
         Current_Cursor := Cursor_At_End_Of (Pack_Names (Pack_Names'First));

         PP_Echo_Cursor_Range (State.Echo_Cursor, Current_Cursor);

         --  Print the package state annotations
         PP_Package_State (Column      => Column_Start,
                           Own         => To_Wide_String (Own_Str),
                           Initializes => To_Wide_String (Init_Str));

         Cursor_Next_Column (Current_Cursor);
         Skip_Blanks (Current_Cursor);
         State.Echo_Cursor := Current_Cursor;
      end;

   end A_Package_Declaration_Pre_Op;

   ---------------------
   -- A_Pragma_Pre_Op --
   ---------------------

   procedure A_Pragma_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);

      Name : constant Wide_String :=
               Pragma_Name_Image (Pragma_Element'(Element));
   begin

      if Cursor_At (Element) < State.Echo_Cursor then
         --  Handling of this pragma was already taken care of
         return;
      end if;

      if Pragma_Kind (Element) = An_Assert_Pragma then
         declare
            Args         : constant Association_List :=
                             Pragma_Argument_Associations (Element);
            Arg          : constant Association :=
                             Argument_By_Name_And_Position
                               (Args, Nil_Name, Check_Position_In_Assert);
            Expr         : constant Asis.Expression := Actual_Parameter (Arg);
            Column_Start : constant Character_Position_Positive :=
                             Element_Span (Element).First_Column;
         begin
            PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));
            PP_Check (Column_Start, Expression_List'(1 => Expr));
            State.Echo_Cursor := Cursor_After (Element);
         end;

      elsif Name = Precondition_Name or else Name = Postcondition_Name then
         PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));
         State.Echo_Cursor := Cursor_After (Element);
      end if;

   end A_Pragma_Pre_Op;

   ------------------------------------------
   -- A_Subprogram_Unit_Declaration_Pre_Op --
   ------------------------------------------

   procedure A_Subprogram_Unit_Declaration_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);

      Column_Start : Character_Position_Positive;
      --  The start position of the "procedure" or "function" keyword,
      --  to align the SPARK contract

      Encl_Element : constant Asis.Element := Enclosing_Element (Element);
      Is_Function  : constant Boolean :=
                       Declaration_Kind (Element) = A_Function_Declaration;
      Pragmas      : constant Pragma_Element_List :=
                       Corresponding_Pragmas (Element);
      Parameters   : constant Asis.Parameter_Specification_List :=
                       Parameter_Profile (Element);
   begin
      if Element_Kind (Encl_Element) = A_Declaration and then
        (Declaration_Kind (Encl_Element) = A_Function_Body_Declaration or else
           Declaration_Kind (Encl_Element) = A_Procedure_Body_Declaration)
      then
         --  Discard declarations of subprograms in a subprogram body, as SPARK
         --  does not allow them

         if Has_SPARK_Contract (Pragmas) then
            --  Output a warning that the corresponding contract is lost in
            --  translation
            SLOC_Warning ("discard contract on declaration inside subprogram",
                          Build_GNAT_Location (Element));
         end if;

         PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));
         State.Echo_Cursor := Cursor_After (Element);

      else

         Column_Start := Element_Span (Element).First_Column;

         --  The parameter lists contains identifiers; they
         --  should be prefixed if needed. To do so, we should call
         --  Traverse_Source on each of them.

         for J in Parameters'Range loop
            Reach_Element_And_Traverse (Parameters (J), State);
         end loop;

         if Is_Function then
            Reach_Element_And_Traverse (Result_Profile (Element), State);
         end if;

         PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_At_End_Of (Element));

         SPARK_Data_Flow (Element     => Element,
                          Is_Function => Is_Function,
                          Column      => Column_Start);

         if Has_SPARK_Contract (Pragmas) then
            SPARK_Contract (Pragmas     => Pragmas,
                            Is_Function => Is_Function,
                            Column      => Column_Start);
         end if;

         State.Echo_Cursor := Cursor_After (Element);

      end if;
   end A_Subprogram_Unit_Declaration_Pre_Op;

   ------------------------------
   -- A_Subprogram_Unit_Pre_Op --
   ------------------------------

   procedure A_Subprogram_Unit_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);

      Column_Start : Character_Position_Positive;
      --  The start position of the "procedure" or "function" keyword,
      --  to align the SPARK contract and the "is" keyword that follows

      Encl_Element : constant Asis.Element := Enclosing_Element (Element);

      Is_Function  : constant Boolean :=
                       Declaration_Kind (Element)
                         = A_Function_Body_Declaration;

      Pragmas      : constant Pragma_Element_List :=
                       Corresponding_Pragmas (Element);

      Params       : constant Parameter_Specification_List :=
                       Parameter_Profile (Element);

      Current_Cursor : Cursor;
   begin
      if Is_Nil (Encl_Element)
        or else Acts_As_Spec (Element)
      then
         --  Only translate contracts on library-level subprograms with no
         --  previous declarations and local subprograms (which do not have
         --  corresponding declarations in SPARK).

         Column_Start := Element_Span (Element).First_Column;

         for J in Params'Range loop
            Reach_Element_And_Traverse (Params (J), State);
         end loop;

         case Declaration_Kind (Element) is
            when A_Procedure_Body_Declaration =>
               if Params'Length = 0 then
                  declare
                     Names : constant Defining_Name_List :=
                       Asis.Declarations.Names (Element);
                  begin
                     pragma Assert (Names'Length = 1);
                     Current_Cursor := Cursor_After (Names (Names'First));
                  end;
               else
                  Current_Cursor := State.Echo_Cursor;
                  Skip_Delimiter (Current_Cursor, Right_Parenthesis_Dlm);
               end if;

            when A_Function_Body_Declaration =>
               Reach_Element_And_Traverse (Result_Profile (Element), State);
               Current_Cursor := State.Echo_Cursor;

            when others =>
               pragma Assert (False);
               null;
         end case;

         PP_Echo_Cursor_Range (State.Echo_Cursor, Current_Cursor);

         SPARK_Data_Flow (Element     => Element,
                          Is_Function => Is_Function,
                          Column      => Column_Start);

         if Has_SPARK_Contract (Pragmas) then

            SPARK_Contract (Pragmas     => Pragmas,
                            Is_Function => Is_Function,
                            Column      => Column_Start);
         end if;

         Cursor_Next_Column (Current_Cursor);
         Skip_Blanks (Current_Cursor);
         State.Echo_Cursor := Current_Cursor;

      else

         if Has_SPARK_Contract (Pragmas) then
            --  Discard contracts on definitions of subprograms, as SPARK
            --  does not allow them

            --  Output a warning that the corresponding contract is lost in
            --  translation
            SLOC_Warning ("discard contract on definition of subprogram",
                          Build_GNAT_Location (Element));
         end if;

      end if;
   end A_Subprogram_Unit_Pre_Op;

   -------------------------------
   -- A_Type_Declaration_Pre_Op --
   -------------------------------

   procedure A_Type_Declaration_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);
      Type_Def     : constant Asis.Definition :=
                       Type_Declaration_View (Element);
      Column_Start : constant Character_Position_Positive :=
                       Element_Span (Element).First_Column;
   begin
      if Cursor_At (Element) < State.Echo_Cursor then
         --  Handling of this Element was already taken care of
         return;
      end if;

      PP_Echo_Cursor_Range
        (State.Echo_Cursor, Cursor_Before (Element));
      State.Echo_Cursor := Cursor_At (Element);

      case Type_Kind (Type_Def) is
         when A_Constrained_Array_Definition =>
            declare
               Array_Type_Str : constant Wide_String :=
                                  Transform_Constrained_Array_Definition
                                    (Type_Def, Column_Start);
            begin
               PP_Echo_Cursor_Range
                 (State.Echo_Cursor, Cursor_Before (Type_Def));
               PP_Word (Array_Type_Str & ";");
               State.Echo_Cursor := Cursor_After (Element);
            end;

         when An_Unconstrained_Array_Definition =>
            declare
               Array_Comp_Def : constant Asis.Component_Definition :=
                                  Array_Component_Definition (Type_Def);
               Array_Comp_Sub : constant Asis.Definition :=
                                  Component_Definition_View (Array_Comp_Def);
               Array_Type_Str : constant Wide_String :=
                                  Transform_Subtype_Indication
                                    (Array_Comp_Sub, Column_Start);
            begin
               --  Treat the type of array components
               case Definition_Kind (Array_Comp_Sub) is
               when A_Subtype_Indication =>
                  PP_Echo_Cursor_Range
                    (State.Echo_Cursor, Cursor_Before (Array_Comp_Sub));
                  PP_Word (Array_Type_Str & ";");
                  State.Echo_Cursor := Cursor_After (Element);
               when others =>
                  SLOC_Error ("unexpected element",
                              Build_GNAT_Location (Element));
               end case;
            end;

         when A_Record_Type_Definition  =>
            declare
               Record_Def    : constant Asis.Definition :=
                                Asis.Definitions.Record_Definition (Type_Def);
               Record_Comps  : constant Asis.Record_Component_List :=
                                     Record_Components (Record_Def);
               Subtype_Names :
                 array (1 .. Record_Comps'Length) of Unbounded_Wide_String;

            begin
               for J in Record_Comps'Range loop
                  declare
                     Comp_Decl  : constant Asis.Declaration :=
                                    Component_Declaration (Record_Comps (J));
                     Object_Def : constant Asis.Definition :=
                                    Object_Declaration_View (Comp_Decl);
                     Comp_View  : constant Asis.Component_Definition :=
                                    Component_Definition_View (Object_Def);
                  begin
                     Subtype_Names (J) := To_Unbounded_Wide_String
                       (Transform_Subtype_Indication
                          (Comp_View, Column_Start));
                  end;
               end loop;

               --  Print up to first record component (IF ANY!!!! Marc, please
               --  check what happens for records with no components)
               PP_Echo_Cursor_Range
                 (State.Echo_Cursor, Cursor_Before (Record_Comps (1)));

               for J in Record_Comps'Range loop
                  declare
                     Comp_Decl  : constant Asis.Declaration :=
                                    Component_Declaration (Record_Comps (J));
                     Object_Def : constant Asis.Definition :=
                                    Object_Declaration_View (Comp_Decl);
                     Comp_View  : constant Asis.Component_Definition :=
                                    Component_Definition_View (Object_Def);
                  begin
                     PP_Echo_Cursor_Range
                       (Cursor_At (Record_Comps (J)),
                        Cursor_Before (Comp_View));
                     PP_Word (To_Wide_String (Subtype_Names (J)));
                     PP_Word (";");
                  end;
               end loop;

               PP_Close_Line;
               PP_Word ("end record;");
               State.Echo_Cursor := Cursor_After (Element);
            end;

         when others =>
            null;
      end case;
   end A_Type_Declaration_Pre_Op;

   ---------------------------------
   -- A_Use_Package_Clause_Pre_Op --
   ---------------------------------

   procedure A_Use_Package_Clause_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);
   begin
      --  Ignore use clauses in SPARK code. Instead, all names should be
      --  prefixed with the packages they come from.
      PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));
      State.Echo_Cursor := Cursor_After (Element);
      Control := Abandon_Children;
   end A_Use_Package_Clause_Pre_Op;

   -------------------------
   -- An_Aggregate_Pre_Op --
   -------------------------

   procedure An_Aggregate_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);
   begin
      if Cursor_At (Element) < State.Echo_Cursor then
         --  Handling of this Element was already taken care of
         return;
      end if;

      declare
         Encl_Element : constant Asis.Element := Enclosing_Element (Element);
      begin
         if Flat_Element_Kind (Encl_Element) = A_Qualified_Expression then
            --  Do nothing because the aggregate is already qualified
            return;
         else
            declare
               Decl_Type : constant Asis.Declaration :=
                             Corresponding_Expression_Type (Element);
               Decl_Name : constant Defining_Name_List :=
                             Asis.Declarations.Names (Decl_Type);
               pragma Assert (Decl_Name'Length = 1);
               Type_Str  : constant Wide_String :=
                             Defining_Name_Image
                             (Decl_Name (Decl_Name'First)) & "'";
            begin
               PP_Echo_Cursor_Range (State.Echo_Cursor,
                                    Cursor_Before (Element));
               PP_Word (Type_Str);

               State.Echo_Cursor := Cursor_At (Element);

            end;
         end if;
      end;

   end An_Aggregate_Pre_Op;

   --------------------------
   -- An_Identifier_Pre_Op --
   --------------------------

   procedure An_Identifier_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);
   begin
      if Cursor_At (Element) < State.Echo_Cursor then
         --  Handling of this identifier was already taken care of
         return;
      end if;

      if Asis.Extensions.Is_Uniquely_Defined (Element) and then
        not Is_Defined_In_Standard_Or_Current_Compilation_Unit (Element) then
         --  Identifier should be prefixed by its package name
         declare
            Decl_Element  : constant Asis.Element :=
                              Corresponding_Name_Declaration (Element);
            Base_Name     : constant Wide_String :=
                              Trim (Element_Image (Element), Ada.Strings.Left);
            Complete_Name : constant Wide_String :=
                              Prepend_Package_Name (Decl_Element, Base_Name);
         begin
            PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));

            PP_Text_At (Line   => First_Line_Number (Element),
                        Column => Element_Span (Element).First_Column,
                        Text   => Complete_Name);

            State.Echo_Cursor := Cursor_After (Element);
         end;
      end if;
   end An_Identifier_Pre_Op;

   ------------------------------------------------
   -- An_Implementation_Defined_Attribute_Pre_Op --
   ------------------------------------------------

   procedure An_Implementation_Defined_Attribute_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);

      Name     : constant Wide_String :=
                   Name_Image (Attribute_Designator_Identifier (Element));
      Prefix_S : constant Wide_String :=
                   State.Prefix (1 .. Integer (State.Prefix_Len));
   begin
      if State.Phase = Printing_Logic then
         if Name = Old_Name then
            PP_Echo_Cursor_Range (State.Echo_Cursor,
                                  Cursor_At_End_Of (Prefix (Element)),
                                  Prefix_S);
            PP_Word ("~");
            State.Echo_Cursor := Cursor_After (Element);

         elsif Name = Result_Name then
            PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element),
                                  Prefix_S);
            PP_Text_At (Line   => First_Line_Number (Element),
                        Column => Element_Span (Element).First_Column,
                        Text   => Result_Name_In_Output,
                        Prefix => Prefix_S);
            State.Echo_Cursor := Cursor_After (Element);
         end if;
      end if;
   end An_Implementation_Defined_Attribute_Pre_Op;

   ----------------------------------
   -- An_Object_Declaration_Pre_Op --
   ----------------------------------

   procedure An_Object_Declaration_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);
      Object_Def   : constant Asis.Definition :=
                       Object_Declaration_View (Element);
      Column_Start : constant Character_Position_Positive :=
                       Element_Span (Element).First_Column;
      Line         : constant Line_Number_Positive :=
                       First_Line_Number (Element);
      Subtype_Name : Unbounded_Wide_String;
   begin
      if Cursor_At (Element) < State.Echo_Cursor then
         --  Handling of this Element was already taken care of
         return;
      end if;

      case Definition_Kind (Object_Def) is
         when A_Subtype_Indication |
              A_Type_Definition =>

            PP_Echo_Cursor_Range
              (State.Echo_Cursor, Cursor_Before (Element));
            State.Echo_Cursor := Cursor_At (Element);

            case Definition_Kind (Object_Def) is
               when A_Subtype_Indication =>

                  if Simple_Subtype_Indication (Object_Def) then
                     return;
                  end if;

                  Subtype_Name :=
                    To_Unbounded_Wide_String
                      (Transform_Subtype_Indication
                           (Object_Def, Column_Start));

               when A_Type_Definition =>
                  pragma Assert
                    (Type_Kind (Object_Def) = A_Constrained_Array_Definition);
                  declare
                     Subtype_Str : constant Wide_String :=
                                     Transform_Constrained_Array_Definition
                                       (Object_Def, Column_Start);
                  begin
                     Subtype_Name := To_Unbounded_Wide_String (Fresh_Name);
                     PP_Text_At (Line, Column_Start,
                                 "type " & To_Wide_String (Subtype_Name)
                                 & " is " & Subtype_Str & ";");
                  end;

               when others =>
                  pragma Assert (False);
                  null;
            end case;

            --  Print the identifier(s) being defined
            PP_Echo_Cursor_Range
              (Cursor_At (Element), Cursor_Before (Object_Def));

            --  Use the new subtype name
            if Flat_Element_Kind (Element) = A_Constant_Declaration then
               PP_Word ("constant " & To_Wide_String (Subtype_Name));
            else
               PP_Word (To_Wide_String (Subtype_Name));
            end if;

            --  Finish printing the declaration
            PP_Echo_Cursor_Range
              (Cursor_After (Object_Def), Cursor_After (Element));
            State.Echo_Cursor := Cursor_After (Element);

         when others =>
            SLOC_Error ("unexpected element",
                        Build_GNAT_Location (Element));
      end case;

   end An_Object_Declaration_Pre_Op;

   -----------------------------------
   -- Argument_By_Name_And_Position --
   -----------------------------------

   function Argument_By_Name_And_Position
     (Args     : Asis.Association_List;
      Name     : Name_String;
      Position : Natural)
      return     Asis.Association
   is
      Arg : Association;
   begin

      for Arg_Idx in Args'Range loop

         Arg := Args (Arg_Idx);

         if Is_Nil (Formal_Parameter (Arg)) then
            --  This is a positional argument
            if Arg_Idx - Args'First = Position then
               return Arg;
            end if;
         else
            --  This is a named argument
            if Element_Image (Formal_Parameter (Arg)) = Name then
               return Arg;
            end if;
         end if;

      end loop;

      pragma Assert (False);
      return Nil_Element;

   end Argument_By_Name_And_Position;

   ------------------------
   -- Has_SPARK_Contract --
   ------------------------

   function Has_SPARK_Contract (Pragmas : Pragma_Element_List) return Boolean
   is
   begin
      for Pragma_Idx in Pragmas'Range loop
         declare
            Pragma_Elt : constant Pragma_Element := Pragmas (Pragma_Idx);
            Name       : constant Wide_String :=
                           Pragma_Name_Image (Pragma_Elt);
         begin
            if Name = Precondition_Name or else Name = Postcondition_Name then
               return True;
            end if;
         end;
      end loop;

      return False;

   end Has_SPARK_Contract;

   --------------------------------------------------------
   -- Is_Defined_In_Standard_Or_Current_Compilation_Unit --
   --------------------------------------------------------

   function Is_Defined_In_Standard_Or_Current_Compilation_Unit
     (Element : Asis.Element) return Boolean
   is
      Decl_Element : Asis.Declaration;
   begin
      case Element_Kind (Element) is
         when An_Expression =>
            Decl_Element := Corresponding_Name_Declaration (Element);
         when A_Declaration =>
            Decl_Element := Element;
         when others =>
            pragma Assert (False);
            null;
      end case;

      if Is_Nil (Decl_Element) then
         return False;
      end if;

      declare
            Element_Unit : constant Asis.Compilation_Unit :=
                             Enclosing_Compilation_Unit (Decl_Element);
            Body_Unit    : constant Asis.Compilation_Unit :=
                             Corresponding_Body (Element_Unit);
            --  Body_Unit might be null or the body unit corresponding to
            --  specification unit Element_Unit
      begin
            return (Is_Standard (Element_Unit) or else
                    Is_Equal (Element_Unit, The_Unit) or else
                    Is_Equal (Body_Unit, The_Unit));
      end;
   end Is_Defined_In_Standard_Or_Current_Compilation_Unit;

   --------------------------
   -- Prepend_Package_Name --
   --------------------------

   function Prepend_Package_Name
     (Element : Asis.Element;
      Name    : Wide_String) return Wide_String
   is
      Encl_Element : Asis.Element;
   begin
      if Is_Nil (Element) then
         return Name;
      end if;

      Encl_Element := Enclosing_Element (Element);

      if Element_Kind (Encl_Element) = A_Declaration and then
        (Declaration_Kind (Encl_Element) = A_Package_Declaration or else
           Declaration_Kind (Encl_Element) = A_Package_Body_Declaration)
      then
         declare
            Names         : constant Defining_Name_List :=
                              Asis.Declarations.Names (Encl_Element);
            pragma Assert (Names'Length = 1);
            Expanded_Name : constant Wide_String :=
                              Defining_Name_Image (Names (Names'First))
                                & "." & Name;
         begin
            if Is_Defined_In_Standard_Or_Current_Compilation_Unit
              (Encl_Element) then
               return Name;
            else
               return Prepend_Package_Name (Encl_Element, Expanded_Name);
            end if;
         end;
      else
         return Name;
      end if;
   end Prepend_Package_Name;

   --------------------------------
   -- Reach_Element_And_Traverse --
   --------------------------------

   procedure Reach_Element_And_Traverse
     (Element : Asis.Element;
      State   : in out Source_Traversal_State)
   is
   begin
      PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));
      Traverse_Element_And_Print (Element);
      State.Echo_Cursor := Cursor_After (Element);
   end Reach_Element_And_Traverse;

   -------------------------------
   -- Simple_Subtype_Indication --
   -------------------------------

   function Simple_Subtype_Indication
     (Element : Subtype_Indication) return Boolean is
   begin
      return Trait_Kind (Element) = An_Ordinary_Trait
        and then Is_Nil (Subtype_Constraint (Element));
   end Simple_Subtype_Indication;

   --------------------
   -- SPARK_Contract --
   --------------------

   procedure SPARK_Contract
     (Pragmas     : Pragma_Element_List;
      Is_Function : Boolean;
      Column      : Character_Position_Positive)
   is
      Pre_Exprs  : Expression_List (1 .. Pragmas'Length);
      Post_Exprs : Expression_List (1 .. Pragmas'Length);
      Pre_Count  : Natural := 0;
      Post_Count : Natural := 0;
   begin
      for Pragma_Idx in Pragmas'Range loop
         declare
            Pragma_Elt : constant Pragma_Element := Pragmas (Pragma_Idx);
            Name       : constant Wide_String :=
                           Pragma_Name_Image (Pragma_Elt);
         begin
            if Name = Precondition_Name or else
              Name = Postcondition_Name then
               declare
                  Args : constant Association_List :=
                           Pragma_Argument_Associations (Pragma_Elt);
                  Arg  : constant Association :=
                           Argument_By_Name_And_Position
                             (Args, Check_Name, Check_Position_In_Prepost);
                  Expr : constant Asis.Expression := Actual_Parameter (Arg);
               begin
                  if Name = Precondition_Name then
                     Pre_Count := Pre_Count + 1;
                     Pre_Exprs (Pre_Count) := Expr;
                  else
                     Post_Count := Post_Count + 1;
                     Post_Exprs (Post_Count) := Expr;
                  end if;
               end;
            end if;
         end;
      end loop;

      if Pre_Count /= 0 then
         PP_Precondition (Column, Pre_Exprs (1 .. Pre_Count));
      end if;
      if Post_Count /= 0 then
         PP_Postcondition (Is_Function, Column, Post_Exprs (1 .. Post_Count));
      end if;
   end SPARK_Contract;

   ---------------------
   -- SPARK_Data_Flow --
   ---------------------

   procedure SPARK_Data_Flow
     (Element     : Asis.Element;
      Is_Function : Boolean;
      Column      : Character_Position_Positive)
   is
      Reads_Str, Writes_Str, Read_Writes_Str : Unbounded_Wide_String;
   begin
      ASIS_UL.Global_State.CG.Sparkify.Global_Effects
        (El              => Element,
         Sep             => ", ",
         Reads_Str       => Reads_Str,
         Writes_Str      => Writes_Str,
         Read_Writes_Str => Read_Writes_Str);

      if Is_Function then
         pragma Assert (Writes_Str = "" and Read_Writes_Str = "");
         null;
      end if;

      PP_Data_Flow (Column        => Column,
                    Global_In     => To_Wide_String (Reads_Str),
                    Global_Out    => To_Wide_String (Writes_Str),
                    Global_In_Out => To_Wide_String (Read_Writes_Str));
   end SPARK_Data_Flow;

   --------------------------------
   -- Transform_A_Discrete_Range --
   --------------------------------

   function Transform_A_Discrete_Range
     (Element       : Asis.Discrete_Range;
      Column_Start  : Character_Position_Positive;
      For_Loop_Mode : Boolean := False) return Wide_String
   is

      function Expr_Has_Universal_Type
        (Expr : Asis.Expression) return Boolean;

      function Expr_Has_Universal_Type
        (Expr : Asis.Expression) return Boolean
      is
         Type_Decl : constant Asis.Declaration :=
                       Corresponding_Expression_Type (Expr);
      begin
         return Is_Root_Num_Type (Type_Decl)
           and then
           Root_Type_Kind (Asis.Set_Get.Root_Type_Definition (Type_Decl))
           = A_Universal_Integer_Definition;
      end Expr_Has_Universal_Type;

      function Corresponding_Type_Of_Range
        (Element : Asis.Discrete_Range) return Asis.Declaration;

      function Corresponding_Type_Of_Range
        (Element : Asis.Discrete_Range) return Asis.Declaration
      is
         LBound_Expr : constant Asis.Expression :=
                         Lower_Bound (Element);
         UBound_Expr : constant Asis.Expression :=
                         Upper_Bound (Element);
         LUniversal  : constant Boolean :=
                         Expr_Has_Universal_Type (LBound_Expr);
         UUniversal  : constant Boolean :=
                         Expr_Has_Universal_Type (UBound_Expr);
      begin
         --  Retrieve type from prefix of range expression
         if LUniversal then
            if UUniversal then
               --  Set Type_Decl to Nil to flag that Name is
               --  already set
               return Nil_Element;
            else
               return Corresponding_Expression_Type (UBound_Expr);
            end if;
         else
            return Corresponding_Expression_Type (LBound_Expr);
         end if;
      end Corresponding_Type_Of_Range;

   begin
      case Discrete_Range_Kind (Element) is
         when A_Discrete_Subtype_Indication =>
            if For_Loop_Mode then
               return "";
            else
               return Transform_Subtype_Indication (Element, Column_Start);
            end if;

         when A_Discrete_Range_Attribute_Reference |
              A_Discrete_Simple_Expression_Range =>
            declare
               Line      : constant Line_Number_Positive :=
                             First_Line_Number (Element);
               Type_Decl : Asis.Declaration;
               Name        : Unbounded_Wide_String;
            begin
               case Discrete_Range_Kind (Element) is
                  when A_Discrete_Range_Attribute_Reference =>
                     declare
                        Expr : constant Asis.Expression :=
                                 Prefix (Range_Attribute (Element));
                     begin
                        --  Retrieve type from prefix of range expression
                        Type_Decl := Corresponding_Expression_Type (Expr);
                        if Is_Nil (Type_Decl) then
                           Type_Decl := Corresponding_Name_Declaration (Expr);
                        end if;

                        declare
                           Type_Def : constant Asis.Definition :=
                                        Type_Declaration_View (Type_Decl);
                        begin
                           case Type_Kind (Type_Def) is
                           when A_Constrained_Array_Definition =>
                              --  Type_Decl is currently an array type, from
                              --  which we should retrieve the appropriate
                              --  index type, depending on the range being
                              --  accessed
                              declare
                                 Index_Def : constant Asis.Definition_List :=
                                     Discrete_Subtype_Definitions (Type_Def);
                              begin
                                 pragma Assert (Index_Def'Length /= 0);

                                 case Discrete_Range_Kind (Index_Def (1)) is
                                    when A_Discrete_Simple_Expression_Range =>
                                       Type_Decl := Corresponding_Type_Of_Range
                                         (Index_Def (1));

                                    when A_Discrete_Subtype_Indication =>
                                       if Is_Nil (Subtype_Constraint
                                                  (Index_Def (1))) then
                                          Type_Decl :=
                                            Corresponding_Expression_Type
                                              (Asis.Definitions.Subtype_Mark
                                                   (Index_Def (1)));
                                             pragma Assert (not Is_Nil (
                                            Type_Decl));
                                       else
                                          declare
                                             Constraint      : constant
                                               Asis.Constraint :=
                                                 Subtype_Constraint
                                                   (Index_Def (1));
                                          begin
                                             case Constraint_Kind
                                               (Constraint) is
                                             when A_Simple_Expression_Range =>
                                                Type_Decl :=
                                                  Corresponding_Type_Of_Range
                                                  (Constraint);
                                             when A_Range_Attribute_Reference
                                                =>
                                                raise Not_Implemented_Yet;
                                             when others =>
                                                pragma Assert (False);
                                                null;
                                             end case;

                                          end;
                                       end if;
                                    when A_Discrete_Range_Attribute_Reference
                                       =>
                                       SLOC_Error ("unexpected element",
                                                   Build_GNAT_Location
                                                     (Element));
                                    when others =>
                                       null;
                                 end case;
                              end;
                           when An_Unconstrained_Array_Definition =>
                              --  Type_Decl is currently an array type, from
                              --  which we should retrieve the appropriate
                              --  index type, depending on the range being
                              --  accessed
                              raise Not_Implemented_Yet;
                           when others =>
                              null;
                           end case;
                        end;
                        pragma Assert (not Is_Nil (Type_Decl));
                     end;

                  when A_Discrete_Simple_Expression_Range =>
                     Type_Decl := Corresponding_Type_Of_Range (Element);
                  when others =>
                     pragma Assert (False);
                     null;
               end case;

               --  If not in the special case where Type_Decl is Nil, then
               --  retrieve the name of the corresponding type
               if not Is_Nil (Type_Decl) then
                  Name := To_Unbounded_Wide_String
                    (Prepend_Package_Name
                       (Type_Decl, Declaration_Unique_Name (Type_Decl)));
               else
                  Name := To_Unbounded_Wide_String ("Integer");
               end if;

               if For_Loop_Mode then
                  return To_Wide_String (Name) & " range ";
               else
                  declare
                     Subtype_Name : constant Wide_String := Fresh_Name;
                  begin
                     --  Print the newly defined subtype
                     PP_Text_At (Line, Column_Start,
                                 "subtype " & Subtype_Name & " is "
                                 & To_Wide_String (Name) & " range ");
                     Traverse_Element_And_Print (Element);
                     PP_Word (";");

                     return Subtype_Name;
                  end;
               end if;
            end;

         when Not_A_Discrete_Range =>
            pragma Assert (False);
            return "";
      end case;
   end Transform_A_Discrete_Range;

   -----------------------------------
   -- Transform_An_Index_Constraint --
   -----------------------------------

   function Transform_An_Index_Constraint
     (Element      : Asis.Constraint;
      Column_Start : Character_Position_Positive) return Wide_String
   is
      Discrete_Range    : constant Asis.Discrete_Range_List :=
                            Discrete_Ranges (Element);
      Encl_Element      : constant Asis.Element :=
                            Enclosing_Element (Element);
      The_Subtype_Name  : constant Asis.Expression :=
                            Asis.Definitions.Subtype_Mark
                              (Encl_Element);
      Constraint_Str    : Unbounded_Wide_String :=
                            To_Unbounded_Wide_String
                              (Element_Name (The_Subtype_Name) & " (");

   begin
      Constraint_Str := Constraint_Str &
      Transform_A_Discrete_Range (Discrete_Range (Discrete_Range'First),
                                  Column_Start);

      for J in Discrete_Range'First + 1 .. Discrete_Range'Last loop
         Constraint_Str := Constraint_Str & ", "
           & Transform_A_Discrete_Range (Discrete_Range (J),
                                         Column_Start);
      end loop;

      Constraint_Str := Constraint_Str & ")";
      return To_Wide_String (Constraint_Str);
   end Transform_An_Index_Constraint;

   --------------------------------------------
   -- Transform_Constrained_Array_Definition --
   --------------------------------------------

   function Transform_Constrained_Array_Definition
     (Element      :        Asis.Type_Definition;
      Column_Start : Character_Position_Positive) return Wide_String
   is
      List_Def       : constant Asis.Definition_List :=
                         Discrete_Subtype_Definitions (Element);
      Array_Comp_Def : constant Asis.Component_Definition :=
                         Array_Component_Definition (Element);
      Array_Comp_Sub : constant Asis.Definition :=
                         Component_Definition_View (Array_Comp_Def);
      Array_Type_Str : Unbounded_Wide_String;
   begin
      pragma Assert (List_Def'Length /= 0);

      --  Treat the types of array indices
      Array_Type_Str := To_Unbounded_Wide_String ("array (")
        & Transform_A_Discrete_Range (List_Def (1), Column_Start);

      for J in List_Def'First + 1 .. List_Def'Last loop
         Array_Type_Str := Array_Type_Str & ", "
           & Transform_A_Discrete_Range (List_Def (J), Column_Start);
      end loop;

      Array_Type_Str := Array_Type_Str & ")";

      --  Treat the type of array components
      case Definition_Kind (Array_Comp_Sub) is
         when A_Subtype_Indication =>
            Array_Type_Str := Array_Type_Str & " of "
              & Transform_Subtype_Indication (Array_Comp_Sub, Column_Start);
         when others =>
            SLOC_Error ("unexpected element",
                        Build_GNAT_Location (Element));
      end case;

      return To_Wide_String (Array_Type_Str);
   end Transform_Constrained_Array_Definition;

   ----------------------------------
   -- Transform_Subtype_Indication --
   ----------------------------------

   function Transform_Subtype_Indication
     (Element      : Subtype_Indication;
      Column_Start : Character_Position_Positive) return Wide_String is
   begin
      --  Reject code with a "non null" trait on a subtype indication
      if Trait_Kind (Element) = A_Null_Exclusion_Trait then
         SLOC_Error ("null exclusion trait",
                     Build_GNAT_Location (Element));
      end if;

      if Is_Nil (Subtype_Constraint (Element)) then
         declare
            Subtype_Expr : constant Asis.Expression :=
                             Asis.Definitions.Subtype_Mark (Element);
         begin
            return Prepend_Package_Name
              (Corresponding_Name_Declaration (Subtype_Expr),
               Element_Name (Subtype_Expr));
         end;
      else
         declare
            Constraint   : constant Asis.Constraint :=
                             Subtype_Constraint (Element);
            Subtype_Name : constant Wide_String := Fresh_Name;
            Subtype_Str  : constant Wide_String :=
                             "subtype " & Subtype_Name & " is ";
            Line         : constant Line_Number_Positive :=
                             First_Line_Number (Element);
         begin
            case Constraint_Kind (Constraint) is
               when A_Range_Attribute_Reference |
                    A_Simple_Expression_Range =>

                  --  Print the newly defined subtype
                  PP_Text_At (Line, Column_Start, Subtype_Str);
                  Traverse_Element_And_Print (Element);
                  PP_Word (";");

               when An_Index_Constraint =>

                  declare
                     Constraint_Str : constant Wide_String :=
                                        Transform_An_Index_Constraint
                                          (Constraint, Column_Start);
                  begin
                     --  Print the newly defined subtype
                     PP_Text_At (Line, Column_Start, Subtype_Str);
                     PP_Word (Constraint_Str & ";");
                  end;

               when A_Digits_Constraint |
                    A_Delta_Constraint =>

                  raise Not_Implemented_Yet;

               when A_Discriminant_Constraint =>

                  SLOC_Error ("discriminant constraint",
                              Build_GNAT_Location (Element));

               when Not_A_Constraint =>

                  pragma Assert (False);
                  null;
            end case;

            return Subtype_Name;
         end;
      end if;
   end Transform_Subtype_Indication;

   ----------------------
   -- Traverse_Element --
   ----------------------

   procedure Traverse_Element_And_Print (Element : Asis.Element)
   is
      Source_Control : Asis.Traverse_Control  := Asis.Continue;
      Source_State   : Source_Traversal_State := Initial_State;
   begin
      Source_State.Echo_Cursor := Cursor_At (Element);
      Traverse_Source (Element, Source_Control, Source_State);
      PP_Echo_Cursor_Range (Source_State.Echo_Cursor,
                            Cursor_At_End_Of (Element));
   end Traverse_Element_And_Print;

end Sparkify.Pre_Operations;
