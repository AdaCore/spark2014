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

with Ada.Strings.Wide_Fixed;           use Ada.Strings.Wide_Fixed;
with Ada.Strings.Wide_Unbounded;       use Ada.Strings.Wide_Unbounded;
with Ada.Integer_Wide_Text_IO;         use Ada.Integer_Wide_Text_IO;

with Asis.Compilation_Units;           use Asis.Compilation_Units;
with Asis.Definitions;                 use Asis.Definitions;
with Asis.Extensions;                  use Asis.Extensions;
with Asis.Text;                        use Asis.Text;
with Asis.Elements;                    use Asis.Elements;
with Asis.Expressions;                 use Asis.Expressions;
with Asis.Declarations;                use Asis.Declarations;
with Asis.Statements;                  use Asis.Statements;
with Asis.Set_Get;                     use Asis.Set_Get;
with Asis.Clauses;                     use Asis.Clauses;

with ASIS_UL.Output;                   use ASIS_UL.Output;
with ASIS_UL.Strings;                  use ASIS_UL.Strings;
with ASIS_UL.Global_State.CG.Sparkify;

with Sparkify.PP_Output;               use Sparkify.PP_Output;
with Sparkify.Names;                   use Sparkify.Names;
with Sparkify.Source_Line_Buffer;      use Sparkify.Source_Line_Buffer;
with Sparkify.Cursors;                 use Sparkify.Cursors;
with Sparkify.Basic;                   use Sparkify.Basic;
with Sparkify.Source_Traversal;        use Sparkify.Source_Traversal;

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

   function Declaration_Complete_Name
     (Element : Asis.Declaration) return Wide_String;

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

   function Is_Defined_In_Standard_Or_Current_Compilation_Unit
     (Element       : Asis.Element;
      Standard_Only : Boolean := False) return Boolean;

   function Prepend_Package_Name
     (Element    : Asis.Element;
      Name       : Wide_String;
      Force      : Boolean := False;
      Subprogram : Boolean := False) return Wide_String;
   --  Functions would be call by an An_Identifier_Pre_Op or others
   --  Methodes where an Identifier should be prefixed by its package name

   procedure Print_An_Association_List (Params : Asis.Association_List);

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
   -- A_Call_Statement_Pre_Op --
   -----------------------------

   procedure A_Call_Statement_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);

      Caller : constant Asis.Declaration :=
                 Corresponding_Called_Entity (Element);
      Params : constant Asis.Association_List :=
                 Call_Statement_Parameters (Statement  => Element,
                                            Normalized => True);
   begin
      --  Do nothing for a dereference or dispatching call
      if not Is_Nil (Caller) then
         PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));
         PP_Text_At (Line            => First_Line_Number (Element),
                     Column          => Element_Span (Element).First_Column,
                     Text            => Declaration_Complete_Name (Caller));
         Print_An_Association_List (Params);
         PP_Word (";");
         State.Echo_Cursor := Cursor_After (Element);
      end if;
   end A_Call_Statement_Pre_Op;

   ----------------------------------
   -- A_Defining_Identifier_Pre_Op --
   ----------------------------------

   procedure A_Defining_Identifier_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);
      Encl_Element : Asis.Element := Enclosing_Element (Element);
   begin
      if Flat_Element_Kind (Encl_Element) = A_Defining_Expanded_Name then
         Encl_Element := Enclosing_Element (Encl_Element);
      end if;

      if Is_Subprogram_Declaration (Encl_Element) then
         declare
            Corresp_Decl : constant Asis.Declaration :=
                            Corresponding_Declaration (Encl_Element);
            Base_Name    : constant Unbounded_Wide_String :=
                             Return_Overloaded_Name (Corresp_Decl);
         begin
            PP_Echo_Cursor_Range (State.Echo_Cursor,
                                  Cursor_Before (Element));

            PP_Text_At (Line   => First_Line_Number (Element),
                        Column => Element_Span (Element).First_Column,
                        Text   => To_Wide_String (Base_Name));

            State.Echo_Cursor := Cursor_After (Element);

            return;
         end;
      end if;
   end A_Defining_Identifier_Pre_Op;

   --------------------------------------
   -- A_Derived_Type_Definition_Pre_Op --
   --------------------------------------

   procedure A_Derived_Type_Definition_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);
      --  get the parent subtype indication by calling
      Subtype_Ind    : constant Asis.Subtype_Indication :=
                         Parent_Subtype_Indication (Element);
      Encl_Element      : constant Asis.Element := Enclosing_Element (Element);
      Encl_Decl_Name : constant Asis.Defining_Name_List :=
                         Asis.Declarations.Names (Encl_Element);
      Subtype_Str    : constant Wide_String := "subtype " & Defining_Name_Image
        (Encl_Decl_Name (Encl_Decl_Name'First)) & " is ";

   begin
      pragma Assert (Encl_Decl_Name'Length = 1);
      if Cursor_At (Element) < State.Echo_Cursor then
         --  Handling of this Element was already taken care of
         return;
      end if;

      PP_Echo_Cursor_Range
        (State.Echo_Cursor, Cursor_Before (Encl_Element));
      PP_Text_At (Line   => First_Line_Number (Encl_Element),
                 Column => Element_Span (Encl_Element).First_Column,
                 Text   => Subtype_Str);
      State.Echo_Cursor := Cursor_At (Subtype_Ind);
   end A_Derived_Type_Definition_Pre_Op;

   ----------------------------
   -- A_Function_Call_Pre_Op --
   ----------------------------

   procedure A_Function_Call_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);

      Caller : constant Asis.Declaration :=
                 Corresponding_Called_Function (Element);
      Params : constant Asis.Association_List :=
                 Function_Call_Parameters (Expression => Element,
                                           Normalized => True);
   begin
      --  Do nothing for a predefined operator
      if not Is_Nil (Caller) then
         PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));
         PP_Text_At (Line            => First_Line_Number (Element),
                     Column          => Element_Span (Element).First_Column,
                     Text            => Declaration_Complete_Name (Caller));
         Print_An_Association_List (Params);
         State.Echo_Cursor := Cursor_After (Element);
      end if;
   end A_Function_Call_Pre_Op;

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

      Pack_Names : constant Defining_Name_List :=
                     Asis.Declarations.Names (Element);
   begin
      if Current_Pass = Printing_Internal then
         declare
            Pack_Name : constant Wide_String :=
                          Flat_Package_Name
                            (Element_Name (Pack_Names (Pack_Names'First)));
         begin
            PP_Echo_Cursor_Range
              (State.Echo_Cursor,
               Cursor_Before (Pack_Names (Pack_Names'First)));

            --  Prefix the name of the internal package to differentiate it
            PP_Word (Internal_Prefix & Pack_Name);

            State.Echo_Cursor := Cursor_After (Pack_Names (Pack_Names'First));
         end;
      end if;
   end A_Package_Declaration_Pre_Op;

   ---------------------------
   -- A_Package_Body_Pre_Op --
   ---------------------------

   procedure A_Package_Body_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);

      Pack_Names : constant Defining_Name_List :=
                     Asis.Declarations.Names (Element);
      pragma Assert (Pack_Names'Length = 1);
   begin
      if Current_Pass = Printing_Internal then
         declare
            Pack_Name : constant Wide_String :=
                          Flat_Package_Name
                            (Element_Name (Pack_Names (Pack_Names'First)));
         begin
            PP_Echo_Cursor_Range
              (State.Echo_Cursor,
               Cursor_Before (Pack_Names (Pack_Names'First)));

            --  Prefix the name of the package to differentiate it
            PP_Word (Internal_Prefix & Pack_Name);

            State.Echo_Cursor := Cursor_After (Pack_Names (Pack_Names'First));
         end;
      end if;
   end A_Package_Body_Pre_Op;

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

   ---------------------------------
   -- A_Selected_Component_Pre_Op --
   ---------------------------------

   procedure A_Selected_Component_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);

      Prefix_Expr : constant Asis.Expression := Prefix (Element);
      Select_Expr : constant Asis.Expression := Selector (Element);

      procedure Skip_Selector;

      procedure Skip_Selector is
      begin
         PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));
         State.Echo_Cursor := Cursor_At (Select_Expr);
      end Skip_Selector;
   begin
      --  Skip package names in prefix position in a selected component
      case Expression_Kind (Prefix_Expr) is
         when An_Identifier =>
            if Is_Package_Name (Prefix_Expr) then
               Skip_Selector;
            end if;
         when A_Selected_Component =>
            if Is_Package_Name (Selector (Prefix_Expr)) then
               Skip_Selector;
            end if;
         when others =>
            null;
      end case;
   end A_Selected_Component_Pre_Op;

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
      Proc_Names   : constant Defining_Name_List :=
                       Asis.Declarations.Names (Element);
      pragma Assert (Proc_Names'Length = 1);
      Proc_Name    : constant Defining_Name :=
                       Proc_Names (Proc_Names'First);
   begin
      if Current_Pass = Printing_Data then
         --  Discard subprograms during data printing
         State.Echo_Cursor := Cursor_After (Element);
         return;
      end if;

      if Current_Pass = Printing_Internal and then
        Element_Kind (Encl_Element) = A_Declaration and then
        (Declaration_Kind (Encl_Element) = A_Function_Body_Declaration
         or else Declaration_Kind (Encl_Element) = A_Procedure_Body_Declaration
         or else Declaration_Kind (Encl_Element) = A_Package_Body_Declaration)
      then
         --  Discard declarations of subprograms in a subprogram body or in
         --  a package body, as SPARK does not allow them

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

         PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Proc_Name));
         PP_Word (To_Wide_String (Return_Overloaded_Name (Element)));
         State.Echo_Cursor := Cursor_After (Proc_Name);

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
      Column_Start   : constant Character_Position_Positive :=
                         Element_Span (Element).First_Column;

      --  The start position of the "procedure" or "function" keyword,
      --  to align the SPARK contract and the "is" keyword that follows

      Encl_Element   : constant Asis.Element := Enclosing_Element (Element);

      Is_Function    : constant Boolean :=
                         Declaration_Kind (Element)
                         = A_Function_Body_Declaration;

      Pragmas        : constant Pragma_Element_List :=
                         Corresponding_Pragmas (Element);

      Params         : constant Parameter_Specification_List :=
                         Parameter_Profile (Element);
      Current_Cursor : Sparkify.Cursors.Cursor;

      Proc_Names     : constant Defining_Name_List :=
                         Asis.Declarations.Names (Element);
      pragma Assert (Proc_Names'Length = 1);
      Proc_Name      : constant Defining_Name :=
                         Proc_Names (Proc_Names'First);

      ------------------------
      -- Set_Current_Cursor --
      ------------------------

      Set_Current_Cursor_Called : Boolean := False;

      procedure Set_Current_Cursor;

      procedure Set_Current_Cursor is
      begin
         if Set_Current_Cursor_Called then
            return;
         end if;
         Set_Current_Cursor_Called := True;

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
      end Set_Current_Cursor;

      --------------------------
      -- Print_SPARK_Contract --
      --------------------------

      procedure Print_SPARK_Contract;

      procedure Print_SPARK_Contract is
      begin
         SPARK_Data_Flow (Element     => Element,
                          Is_Function => Is_Function,
                          Column      => Column_Start);

         if Has_SPARK_Contract (Pragmas) then

            SPARK_Contract (Pragmas     => Pragmas,
                            Is_Function => Is_Function,
                            Column      => Column_Start);
         end if;
      end Print_SPARK_Contract;
   begin
      if Current_Pass = Printing_Data then
         --  Discard subprograms during data printing
         State.Echo_Cursor := Cursor_After (Element);
         return;
      end if;

      if Current_Pass = Printing_External
        and then Is_Package_Level_Element (Element) then
         --  When printing the external package, ignore subprograms bodies that
         --  are only defined in the internal package, but print a declaration
         --  for those bodies without a corresponding declaration.

         if Acts_As_Spec (Element) then
            --  Subprogram defintion serves as declaration
            PP_Echo_Cursor_Range
              (State.Echo_Cursor, Cursor_Before (Proc_Name));
            PP_Word (To_Wide_String (Return_Overloaded_Name (Element)));
            State.Echo_Cursor := Cursor_After (Proc_Name);

            Set_Current_Cursor;
            PP_Word (";");
            Print_SPARK_Contract;
         else
            PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));
         end if;

         State.Echo_Cursor := Cursor_After (Element);

         return;
      end if;

      if Is_Nil (Encl_Element)
        or else Acts_As_Spec (Element)
      then
         --  Only translate contracts on library-level subprograms with no
         --  previous declarations and local subprograms (which do not have
         --  corresponding declarations in SPARK).

         --  Subprogram defintion serves as declaration
         PP_Echo_Cursor_Range  (State.Echo_Cursor, Cursor_Before (Proc_Name));
         PP_Word (To_Wide_String (Return_Overloaded_Name (Element)));
         State.Echo_Cursor := Cursor_After (Proc_Name);

         Set_Current_Cursor;
         Print_SPARK_Contract;
         Cursor_Next_Column (Current_Cursor);
         Skip_Blanks (Current_Cursor);
         State.Echo_Cursor := Current_Cursor;
      else
         PP_Echo_Cursor_Range  (State.Echo_Cursor, Cursor_Before (Proc_Name));
         Traverse_Element_And_Print (Proc_Name);
         State.Echo_Cursor := Cursor_After (Proc_Name);

         if Has_SPARK_Contract (Pragmas) then
            --  Discard contracts on definitions of subprograms, as SPARK
            --  does not allow them

            --  Output a warning that the corresponding contract is lost in
            --  translation
            SLOC_Warning ("discard contract on definition of subprogram",
                          Build_GNAT_Location (Element));
         end if;

      end if;

      --  First print local non-subprograms, then print local subprograms,
      --  to comply with SPARK division between declarations

      declare
         procedure Print_Decl_List
           (Decl_Items        : Asis.Declarative_Item_List;
            Print_Subprograms : Boolean);

         procedure Print_Decl_List
           (Decl_Items        : Asis.Declarative_Item_List;
            Print_Subprograms : Boolean) is
         begin
            for J in Decl_Items'Range loop
               if Print_Subprograms =
                 Is_Subprogram_Declaration (Decl_Items (J))
               then
                  Pre_Operations.Traverse_Element_And_Print (Decl_Items (J));
               end if;
            end loop;
         end Print_Decl_List;

         Decl_Items : constant Declarative_Item_List :=
                        Body_Declarative_Items
                          (Declaration => Element, Include_Pragmas => False);
      begin
         if Decl_Items'Length /= 0 then
            Set_Current_Cursor;
            PP_Word_Alone_On_Line_At (Column_Start, "is");

            Print_Decl_List (Decl_Items, Print_Subprograms => False);
            Print_Decl_List (Decl_Items, Print_Subprograms => True);

            State.Echo_Cursor := Cursor_After (Decl_Items (Decl_Items'Last));
         end if;
      end;

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
      if Current_Pass in Printing_Subprograms
        and then Is_Package_Level_Element (Element) then
         --  When printing subprograms, ignore types that are already defined
         --  in the data package
         PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));
         State.Echo_Cursor := Cursor_After (Element);
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
                  SLOC_Error_And_Exit ("unexpected element",
                                       Build_GNAT_Location (Element));
               end case;
            end;

         when A_Record_Type_Definition  =>
            declare
               Record_Def : constant Asis.Definition :=
                              Asis.Definitions.Record_Definition (Type_Def);
            begin
               --  In SPARK, a record definition cannot be a null record
               --  unless it is tagged
               if Definition_Kind (Record_Def) = A_Null_Record_Definition then
                  if Flat_Element_Kind (Record_Def) =
                    A_Tagged_Record_Type_Definition then
                     return;
                  else
                     SLOC_Error_And_Exit ("!!!null record definition",
                                          Build_GNAT_Location (Element));
                  end if;
               end if;

               declare
                  Record_Comps  : constant Asis.Record_Component_List :=
                                    Record_Components (Record_Def);
                  Subtype_Names :
                    array (1 .. Record_Comps'Length) of Unbounded_Wide_String;
               begin
                  --  In SPARK, a component list cannot be null unless
                  --  the record is tagged
                  if (Record_Comps'Length = 1) and then
                    Flat_Element_Kind
                      (Component_Declaration (Record_Comps (1)))
                      = A_Null_Component
                  then
                     if Flat_Element_Kind (Record_Def) =
                       A_Tagged_Record_Type_Definition then
                        return;
                     else
                        SLOC_Error_And_Exit ("!!!null component in record",
                                             Build_GNAT_Location (Element));
                     end if;
                  end if;

                  for J in Record_Comps'Range loop
                     declare
                        Comp_Decl  : constant Asis.Declaration
                          := Component_Declaration (Record_Comps (J));
                        Object_Def : constant Asis.Definition
                          := Object_Declaration_View (Comp_Decl);
                        Comp_View  : constant Asis.Component_Definition
                          := Component_Definition_View (Object_Def);
                     begin
                        Subtype_Names (J) := To_Unbounded_Wide_String
                          (Transform_Subtype_Indication
                             (Comp_View, Column_Start));
                     end;
                  end loop;

                  PP_Echo_Cursor_Range
                    (State.Echo_Cursor, Cursor_Before (Record_Comps (1)));

                  for J in Record_Comps'Range loop
                     declare
                        Comp_Decl  : constant Asis.Declaration
                          := Component_Declaration (Record_Comps (J));
                        Object_Def : constant Asis.Definition
                          := Object_Declaration_View (Comp_Decl);
                        Comp_View  : constant Asis.Component_Definition
                          := Component_Definition_View (Object_Def);
                     begin
                        PP_Echo_Cursor_Range
                          (Cursor_At (Record_Comps (J)),
                           Cursor_Before (Comp_View));
                        PP_Word (To_Wide_String (Subtype_Names (J)));
                        PP_Word (";");
                     end;
                  end loop;
               end;

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

   -----------------------
   -- A_Use_Type_Pre_Op --
   -----------------------

   procedure A_Use_Type_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State) is
   begin
      --  Ignore use types in SPARK code. Instead, they are automatically
      --  added when with'ing the corresponding package.
      PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));
      State.Echo_Cursor := Cursor_After (Element);
      Control := Abandon_Children;
   end A_Use_Type_Pre_Op;

   ----------------------------------
   -- A_With_Package_Clause_Pre_Op --
   ----------------------------------

   procedure A_With_Package_Clause_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);

      Names : constant Asis.Name_List := Clause_Names (Element);
      Decl  : Asis.Declaration;

      function Get_Pack_Name (Expr : Asis.Expression) return Asis.Expression;

      function Get_Pack_Name (Expr : Asis.Expression) return Asis.Expression is
      begin
         case Expression_Kind (Expr) is
            when An_Identifier =>
               return Expr;
            when A_Selected_Component =>
               return Get_Pack_Name (Selector (Expr));
            when An_Attribute_Reference =>
               SLOC_Error_And_Exit ("unexpected element",
                                    Build_GNAT_Location (Element));
            when others =>
               pragma Assert (False);
               return Nil_Element;
         end case;
      end Get_Pack_Name;
   begin
      PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));

      for Name in Names'Range loop
         declare
            Pack_Id   : constant Asis.Expression :=
                          Get_Pack_Name (Names (Name));
            Pack_Name : constant Wide_String := Get_Package_Name (Pack_Id);
         begin
            PP_Close_Line;
            PP_Word ("with " & Pack_Name & ";");
            --  Add all possible use-type clauses in SPARK code, to make for
            --  the absence of a use-package clauses.
            Decl := Corresponding_Name_Declaration (Pack_Id);
            Print_All_Use_Type (Decl);

            if Current_Pass = Printing_Internal then
               PP_Word_Alone_On_Line
                 ("with " & External_Prefix & Pack_Name & ";");
            end if;
         end;
      end loop;

      State.Echo_Cursor := Cursor_After (Element);
   end A_With_Package_Clause_Pre_Op;

   -------------------------
   -- An_Aggregate_Pre_Op --
   -------------------------

   procedure An_Aggregate_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);

      --  It may occur that the name does not exist in the original source code
      --  but we created it instead during the translation. Try to retrieve it
      --  from the map which was created by the translation.
      function Get_Type_Name_From_Context
        (Element : Asis.Element) return Wide_String;

      function Get_Type_Name_From_Context
        (Element : Asis.Element) return Wide_String
      is
         Encl_Element : constant Asis.Element := Enclosing_Element (Element);
         Var_Decl     : Asis.Declaration;
      begin
         case Element_Kind (Encl_Element) is
            when A_Declaration =>
               Var_Decl := Encl_Element;

            when A_Statement =>
               case Statement_Kind (Encl_Element) is
                  when An_Assignment_Statement =>
                     declare
                        Var_Expr : constant Asis.Expression :=
                                     Assignment_Variable_Name (Encl_Element);
                     begin
                        Var_Decl := Corresponding_Name_Declaration (Var_Expr);
                     end;
                  when others =>
                     raise Not_Implemented_Yet;
               end case;

            when others =>
               raise Not_Implemented_Yet;
         end case;

         declare
            Name : constant Wide_String :=
                     To_Wide_String (Get_New_Name (Var_Decl));
         begin
            if Name /= "" then
               --  We defined a new name for the type corresponding to
               --  this declaration, so use it here.
               return Name;
            else
               raise Not_Implemented_Yet;
            end if;
         end;
      end Get_Type_Name_From_Context;

      Encl_Element : constant Asis.Element := Enclosing_Element (Element);
      Type_Decl    : constant Asis.Declaration :=
                       Corresponding_Expression_Type (Element);
      Type_Str     : Unbounded_Wide_String;
   begin

      if Flat_Element_Kind (Encl_Element) = A_Qualified_Expression then
         --  Do nothing because the aggregate is already qualified
         return;
      elsif Is_Nil (Type_Decl) or else
        Type_Kind (Type_Declaration_View (Type_Decl))
        = An_Unconstrained_Array_Definition
      then
         Type_Str :=
           To_Unbounded_Wide_String (Get_Type_Name_From_Context (Element));
      else
         declare
            Decl_Name : constant Defining_Name_List :=
                          Asis.Declarations.Names (Type_Decl);
            pragma Assert (Decl_Name'Length = 1);
            Base_Name : constant Wide_String :=
                          Defining_Name_Image (Decl_Name (Decl_Name'First));
            Full_Name : constant Wide_String :=
                          Prepend_Package_Name (Type_Decl, Base_Name);
         begin
            Type_Str := To_Unbounded_Wide_String (Full_Name);
         end;
      end if;

      PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));
      PP_Word (To_Wide_String (Type_Str) & "'");
      State.Echo_Cursor := Cursor_At (Element);

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

      Base_Name : Unbounded_Wide_String :=
                    To_Unbounded_Wide_String (Element_Name (Element));
   begin
      if Asis.Extensions.Is_Uniquely_Defined (Element) then

         if Is_Subprogram_Name (Element) then
            declare
               Corresp_Decl : constant Asis.Declaration :=
                                Corresponding_Name_Declaration (Element);
            begin
               Base_Name := Return_Overloaded_Name (Corresp_Decl);
            end;
         elsif Is_Package_Name (Element) then
            --  Full name of the package should be used
            declare
               Pack_Name : constant Wide_String := Get_Package_Name (Element);
            begin
               PP_Echo_Cursor_Range
                 (State.Echo_Cursor, Cursor_Before (Element));
               PP_Text_At (Line   => First_Line_Number (Element),
                           Column => Element_Span (Element).First_Column,
                           Text   => Pack_Name);

               State.Echo_Cursor := Cursor_After (Element);

               return;
            end;
         end if;

         if Is_Defined_In_Standard_Or_Current_Compilation_Unit (Element) then
            if Base_Name =
              To_Unbounded_Wide_String (Element_Name (Element))
            then
               return;
            else
               PP_Echo_Cursor_Range
                 (State.Echo_Cursor, Cursor_Before (Element));

               PP_Text_At (Line   => First_Line_Number (Element),
                           Column => Element_Span (Element).First_Column,
                           Text   => To_Wide_String (Base_Name));

               State.Echo_Cursor := Cursor_After (Element);

               return;
            end if;
         end if;

         --  Identifier should be prefixed by its package name
         declare
            Complete_Name : constant Wide_String :=
                              Prepend_Package_Name
                                (Element, To_Wide_String (Base_Name));
            Prefix_S      : constant Wide_String :=
                              State.Prefix (1 .. Integer (State.Prefix_Len));
         begin
            PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element),
                                  Prefix_S);

            PP_Text_At (Line   => First_Line_Number (Element),
                        Column => Element_Span (Element).First_Column,
                        Text   => Complete_Name,
                        Prefix => Prefix_S);

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
            Reach_Element_And_Traverse (Prefix (Element), State);
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
      if Current_Pass in Printing_Subprograms
        and then Is_Package_Level_Element (Element) then
         --  When printing subprograms, ignore objects that are already defined
         --  in the data package
         PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));
         State.Echo_Cursor := Cursor_After (Element);
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

                  Subtype_Name := To_Unbounded_Wide_String
                    (Transform_Subtype_Indication (Object_Def, Column_Start));

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

            --  Finish printing the object
            State.Echo_Cursor := Cursor_After (Object_Def);

            --  Record that a new name was (possibly) created for
            --  the declaration. If this was not the case, store the existing
            --  name anyway.
            Store_New_Name (Element, Subtype_Name);

         when others =>
            SLOC_Error_And_Exit ("unexpected element",
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

   -------------------------------
   -- Declaration_Complete_Name --
   -------------------------------

   function Declaration_Complete_Name
     (Element : Asis.Declaration) return Wide_String
   is
      Names : constant Defining_Name_List := Asis.Declarations.Names (Element);
      pragma Assert (Names'Length = 1);
      Base_Name : Unbounded_Wide_String :=
                    To_Unbounded_Wide_String
                      (Defining_Name_Image (Names (Names'First)));
   begin
      if Is_Subprogram_Declaration (Element) then
         Base_Name := Return_Overloaded_Name (Element);
      end if;

      if Is_Defined_In_Standard_Or_Current_Compilation_Unit
        (Element, Standard_Only => True) then
         return To_Wide_String (Base_Name);
      else
         --  Identifier should be prefixed by its package name
         return Prepend_Package_Name
           (Element, To_Wide_String (Base_Name), Force => True);
      end if;
   end Declaration_Complete_Name;

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
     (Element       : Asis.Element;
      Standard_Only : Boolean := False) return Boolean
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
         Pack_Element : constant Asis.Element :=
                          Unit_Declaration (Element_Unit);
         Body_Unit    : constant Asis.Compilation_Unit :=
                          Corresponding_Body (Element_Unit);
         --  Body_Unit might be null or the body unit corresponding to
         --  specification unit Element_Unit

         Def_In_Standard : constant Boolean := Is_Standard (Element_Unit);
         Def_In_Cur_Spec : Boolean;
         Def_In_Cur_Body : Boolean;
         Def_In_Current  : Boolean;
      begin
         Def_In_Cur_Spec :=
           (Declaration_Kind (Pack_Element) = A_Package_Declaration
            and then Is_Equal (Element_Unit, The_Unit))
           or else
           (not Is_Nil (Body_Unit)
            and then
              Declaration_Kind (Unit_Declaration (Body_Unit)) =
              A_Package_Body_Declaration
            and then Is_Equal (Body_Unit, The_Unit));

         Def_In_Cur_Body :=
           Declaration_Kind (Pack_Element) = A_Package_Body_Declaration
           and then Is_Equal (Element_Unit, The_Unit);

         Def_In_Current :=
           not Standard_Only and then
           (Def_In_Cur_Spec or else Def_In_Cur_Body);

         if Current_Pass in Printing_Subprograms then
            --  When printing subprograms, new packages are created, which only
            --  call and reference the original body in their expressions
            case Element_Kind (Element) is
               when An_Expression =>
                  return Def_In_Standard;
               when A_Declaration =>
                  case Declaration_Kind (Element) is
                     when A_Function_Declaration |
                          A_Procedure_Declaration =>
                        return Def_In_Standard or else Def_In_Current;
                     when others =>
                        return Def_In_Standard;
                  end case;
               when others =>
                  pragma Assert (False);
                  return False;
            end case;
         else
            return Def_In_Standard or else Def_In_Current;
         end if;
      end;
   end Is_Defined_In_Standard_Or_Current_Compilation_Unit;

   --------------------------
   -- Prepend_Package_Name --
   --------------------------

   function Prepend_Package_Name
     (Element    : Asis.Element;
      Name       : Wide_String;
      Force      : Boolean := False;
      Subprogram : Boolean := False) return Wide_String
   is
      Decl_Element : Asis.Declaration;
      Encl_Element : Asis.Element;

      function Return_Name return Wide_String;

      function Return_Name return Wide_String is
      begin
         if Subprogram then
            return External_Prefix & Name;
         else
            return Name;
         end if;
      end Return_Name;
   begin
      if not Force and then
        Is_Defined_In_Standard_Or_Current_Compilation_Unit (Element) then
         return Name;
      end if;

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
         return Return_Name;
      end if;

      Encl_Element := Enclosing_Element (Decl_Element);
      if Flat_Element_Kind (Element) = An_Enumeration_Literal then
         --  Encl_Element is just the aggregate of enumeration literals.
         --  Retrieve successively the type and the enclosing entity.
         Encl_Element := Enclosing_Element (Enclosing_Element (Encl_Element));
      end if;

      if Is_Package_Declaration (Encl_Element) then
         declare
            Names         : constant Defining_Name_List :=
                              Asis.Declarations.Names (Encl_Element);
            pragma Assert (Names'Length = 1);
            Dot           : constant Wide_String :=
                              (if Is_Package_Declaration (Element) then "_"
                               else ".");
            Pack_Name     : constant Wide_String :=
                              Flat_Package_Name
                                (Defining_Name_Image (Names (Names'First)));
            Expanded_Name : constant Wide_String := Pack_Name & Dot & Name;
            Is_Subprogram : constant Boolean :=
                              Subprogram or else
                              Is_Subprogram_Declaration (Decl_Element);
         begin
            return Prepend_Package_Name (Encl_Element, Expanded_Name, Force,
                                         Is_Subprogram);
         end;
      else
         return Return_Name;
      end if;
   end Prepend_Package_Name;

   ------------------------
   -- Print_All_Use_Type --
   ------------------------

   procedure Print_All_Use_Type (Element : Asis.Declaration) is
      Private_Items : constant Declarative_Item_List :=
                        Private_Part_Declarative_Items
                          (Declaration => Element, Include_Pragmas => False);
      Visible_Items : constant Declarative_Item_List :=
                        Visible_Part_Declarative_Items
                          (Declaration => Element, Include_Pragmas => False);
      Decl_Items    : constant Declarative_Item_List :=
                        Private_Items & Visible_Items;
   begin
      for J in Decl_Items'Range loop
         declare
            Type_Decl : constant Asis.Declaration := Decl_Items (J);
         begin
            case Declaration_Kind (Type_Decl) is
               when A_Type_Declaration =>
                  if Type_Kind (Type_Declaration_View (Type_Decl))
                    /= A_Derived_Type_Definition then
                     PP_Word ("use type "
                       & Prepend_Package_Name
                         (Type_Decl, Declaration_Unique_Name (Type_Decl),
                          Force => True)
                       & "; ");
                     PP_Close_Line;
                  end if;
               when others =>
                  null;
            end case;
         end;
      end loop;
   end Print_All_Use_Type;

   -------------------------------
   -- Print_An_Association_List --
   -------------------------------

   procedure Print_An_Association_List (Params : Asis.Association_List) is
   begin
      if not Is_Nil (Params) then
         declare
            First_Param : constant Asis.Association := Params (Params'First);
         begin
            PP_Word ("(");
            PP_Word (Element_Name (Formal_Parameter (First_Param)));
            PP_Word (" => ");
            Traverse_Element_And_Print (Actual_Parameter (First_Param));

            for J in Params'First + 1 .. Params'Last loop
               PP_Word (", ");
               PP_Word (Element_Name (Formal_Parameter (Params (J))));
               PP_Word (" => ");
               Traverse_Element_And_Print (Actual_Parameter (Params (J)));
            end loop;

            PP_Word (")");
         end;
      end if;
   end Print_An_Association_List;

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

      function Index_Type_Of_Array_Type_Declaration
        (Type_Def : Asis.Definition; Index_Ref : Positive)
         return Asis.Declaration;

      function Index_Type_Of_Array_Type_Declaration
        (Type_Def : Asis.Definition; Index_Ref : Positive)
         return Asis.Declaration
      is
         Type_Decl : Asis.Declaration;
      begin

         case Type_Kind (Type_Def) is
            when A_Constrained_Array_Definition =>
               declare
                  Index_Def : constant Asis.Definition :=
                                Discrete_Subtype_Definitions
                                  (Type_Def) (Index_Ref);
               begin
                  case Discrete_Range_Kind (Index_Def) is
                  when A_Discrete_Simple_Expression_Range =>
                     Type_Decl := Corresponding_Type_Of_Range (Index_Def);

                  when A_Discrete_Subtype_Indication =>
                     Type_Decl :=
                       Corresponding_Name_Declaration
                         (Asis.Definitions.Subtype_Mark (Index_Def));
                     pragma Assert (not Is_Nil (Type_Decl));

                  when others =>
                     SLOC_Error_And_Exit ("unexpected element",
                                          Build_GNAT_Location (Element));
                  end case;
               end;

            when An_Unconstrained_Array_Definition =>
               declare
                  Index_Def : constant Asis.Expression :=
                                Index_Subtype_Definitions
                                  (Type_Def) (Index_Ref);
               begin
                  Type_Decl := Corresponding_Name_Declaration (Index_Def);
                  pragma Assert (not Is_Nil (Type_Decl));
               end;

            when others =>
               pragma Assert (False);
               null;
         end case;

         return Type_Decl;
      end Index_Type_Of_Array_Type_Declaration;

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
               Line        : constant Line_Number_Positive :=
                               First_Line_Number (Element);
               Type_Decl   : Asis.Declaration;
               Name        : Unbounded_Wide_String;
            begin
               case Discrete_Range_Kind (Element) is
                  when A_Discrete_Range_Attribute_Reference =>
                     declare
                        Expr_Att  : constant Asis.Expression :=
                                      Range_Attribute (Element);
                        Expr      : constant Asis.Expression :=
                                      Prefix (Expr_Att);
                        Att       : constant Asis.Expression_List :=
                                      Attribute_Designator_Expressions
                                        (Expr_Att);
                        Index_Ref : Positive;
                     begin
                        --  Retrieve type from prefix of range expression
                        Type_Decl := Corresponding_Expression_Type (Expr);
                        if Is_Nil (Type_Decl) then
                           Type_Decl := Corresponding_Name_Declaration (Expr);
                        end if;

                        if Att = Nil_Element_List then
                           Index_Ref := 1;
                        else
                           declare
                              pragma Assert (Att'Length = 1);
                              Att_Value : constant Wide_String :=
                                            Trim
                                              (Static_Expression_Value_Image
                                                 (Att (1)), Ada.Strings.Left);
                              Last      : Positive;
                           begin
                              pragma Assert (Att_Value /= "");
                              Ada.Integer_Wide_Text_IO.Get
                                (Att_Value, Index_Ref, Last);
                              pragma Assert (Last = Att_Value'Length);
                           end;
                        end if;

                        declare
                           Type_Def : constant Asis.Definition :=
                                        Type_Declaration_View (Type_Decl);
                        begin
                           case Type_Kind (Type_Def) is
                           when A_Constrained_Array_Definition |
                                An_Unconstrained_Array_Definition =>
                              --  Type_Decl is currently an array type, from
                              --  which we should retrieve the appropriate
                              --  index type, depending on the range being
                              --  accessed
                              Type_Decl :=
                                Index_Type_Of_Array_Type_Declaration
                                     (Type_Def, Index_Ref);
                           when others =>
                              null;
                           end case;
                        end;
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
      Subtype_Name      : constant Asis.Expression :=
                            Asis.Definitions.Subtype_Mark
                              (Encl_Element);
      Subtype_Decl      : constant Asis.Declaration :=
                            Corresponding_Name_Declaration (Subtype_Name);
      Subtype_Str       : constant Wide_String :=
                            Prepend_Package_Name
                              (Subtype_Decl, Element_Name (Subtype_Name));
      Constraint_Str    : Unbounded_Wide_String :=
                            To_Unbounded_Wide_String (Subtype_Str & " (");

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
            SLOC_Error_And_Exit ("unexpected element",
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
         SLOC_Error_And_Exit ("null exclusion trait",
                              Build_GNAT_Location (Element));
      end if;

      if Is_Nil (Subtype_Constraint (Element)) then
         declare
            Subtype_Expr : constant Asis.Expression :=
                             Skip_Package_Names
                               (Asis.Definitions.Subtype_Mark (Element));
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

                  SLOC_Error_And_Exit ("discriminant constraint",
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
