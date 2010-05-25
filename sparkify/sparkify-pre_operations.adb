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
with ASIS_UL.Output;                   use ASIS_UL.Output;
with ASIS_UL.Strings;                  use ASIS_UL.Strings;
with Asis.Set_Get;                     use Asis.Set_Get;

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

   function Transform_Subtype_Indication
     (Discrete_Subtype : Asis.Element)
      return Wide_String;
   --  Return the subtype indication's identifier or create new subtype name

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

   --------------------
   -- SPARK_Contract --
   --------------------

   procedure SPARK_Contract
     (Pragmas     : Pragma_Element_List;
      Is_Function : Boolean;
      Column      : Character_Position_Positive) is
   begin

      for Pragma_Idx in Pragmas'Range loop
         declare
            Pragma_Elt : constant Pragma_Element := Pragmas (Pragma_Idx);
            Name       : constant Wide_String :=
                           Pragma_Name_Image (Pragma_Elt);
         begin

            if Name = Precondition_Name or else Name = Postcondition_Name then
               declare
                  Args : constant Association_List :=
                           Pragma_Argument_Associations (Pragma_Elt);
                  Arg  : constant Association := Argument_By_Name_And_Position
                           (Args, Check_Name, Check_Position_In_Prepost);
                  Expr : constant Asis.Expression := Actual_Parameter (Arg);
               begin
                  if Name = Precondition_Name then
                     PP_Precondition (Column, Expr);
                  else
                     PP_Postcondition (Is_Function, Column, Expr);
                  end if;
               end;

            end if;
         end;
      end loop;

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

   --------------------------------------------------------
   -- Is_Defined_In_Standard_Or_Current_Compilation_Unit --
   --------------------------------------------------------

   function Is_Defined_In_Standard_Or_Current_Compilation_Unit
     (Element : Asis.Element) return Boolean
   is
      Decl_Element : constant Asis.Element :=
        Corresponding_Name_Declaration (Element);
   begin
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
            return Prepend_Package_Name (Encl_Element, Expanded_Name);
         end;
      else
         return Name;
      end if;
   end Prepend_Package_Name;

   ----------------------------------
   -- Transform_Subtype_Indication --
   ----------------------------------

   function Transform_Subtype_Indication
     (Discrete_Subtype : Asis.Discrete_Subtype_Definition)
      return Wide_String
   is
      Base_Name     : constant Wide_String :=
        Trim (Element_Image (Discrete_Subtype),
              Ada.Strings.Both);
      Complete_Name : constant Wide_String :=
        Prepend_Package_Name
          (Discrete_Subtype, Base_Name);
   begin
      if Flat_Element_Kind (Discrete_Subtype) =
        A_Subtype_Indication
        or
        Flat_Element_Kind (Discrete_Subtype) =
        A_Discrete_Subtype_Indication_As_Subtype_Definition
      then
         declare
            Constraint : constant Asis.Constraint :=
              Subtype_Constraint (Discrete_Subtype);
         begin
            if Flat_Element_Kind (Constraint) = A_Simple_Expression_Range then
               return Fresh_Name;

            elsif Flat_Element_Kind (Constraint) = An_Index_Constraint then
               return Fresh_Name;

            elsif Flat_Element_Kind (Constraint)
              = A_Range_Attribute_Reference then
               return "No treat A_Range_Attribute_Reference";

            elsif Flat_Element_Kind (Constraint) = A_Digits_Constraint then
               return "No treat A_Digits_Constraint";

               --  See others cases
            else

               return Complete_Name;
            end if;
         end;

      elsif Flat_Element_Kind (Discrete_Subtype) =
        A_Discrete_Simple_Expression_Range_As_Subtype_Definition then
         return Fresh_Name;

      else
            return Complete_Name;
      end if;

   end Transform_Subtype_Indication;

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
            Iter_Scheme : constant Asis.Element :=
              Get_Iteration_Scheme (Element);
         begin
            --  Update this kinds to insert the type in for loop
            if Flat_Element_Kind (Iter_Scheme) =
              A_Loop_Parameter_Specification then
               declare
                  Discrete_Subtype_Def : constant
                    Asis.Discrete_Subtype_Definition :=
                      Specification_Subtype_Definition (Iter_Scheme);
               begin
                  if Flat_Element_Kind (Discrete_Subtype_Def) =
                    A_Discrete_Simple_Expression_Range_As_Subtype_Definition
                  then
                     declare
                        Lower_Expr : constant Asis.Expression :=
                          Lower_Bound (Discrete_Subtype_Def);
                     begin
                           PP_Echo_Cursor_Range (State.Echo_Cursor,
                                                 Cursor_Before
                                                   (Discrete_Subtype_Def));
                        State.Echo_Cursor := Cursor_After
                          (Discrete_Subtype_Def);
                        --  Just a test, see a others cases
                        if Flat_Element_Kind (Lower_Expr) =
                          An_Integer_Literal then
                           PP_Word (" Integer range ");
                        end if;
                        Reach_Element_And_Traverse
                          (Discrete_Subtype_Def, State);
                     end;
                  elsif Flat_Element_Kind (Discrete_Subtype_Def) =
                    A_Discrete_Range_Attribute_Reference_As_Subtype_Definition
                  then
                     declare
                        Att_Range : constant Asis.Expression :=
                          Range_Attribute (Discrete_Subtype_Def);
--                          Att_Prefix : constant Asis.Expression :=
--                            Prefix (Att_Range);
                     begin
                        PP_Echo_Cursor_Range (State.Echo_Cursor,
                                              Cursor_Before
                                                (Discrete_Subtype_Def));
                        State.Echo_Cursor := Cursor_After
                          (Discrete_Subtype_Def);
                        --  Just an test see others cases
                        if Flat_Element_Kind (Att_Range) =
                          A_Range_Attribute then
                           PP_Word (" Integer range ");
                        end if;
                        Reach_Element_And_Traverse
                          (Discrete_Subtype_Def, State);
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
         end;
      end if;

      if Statements'First <= Last_Pragma_Index then
         declare
            Pragmas : constant Pragma_Element_List :=
                        Statements (Statements'First .. Last_Pragma_Index);
         begin
            PP_Echo_Cursor_Range
              (State.Echo_Cursor, Cursor_Before (Pragmas (Pragmas'First)));

            for Index in Pragmas'Range loop
               if Pragma_Kind (Pragmas (Index)) = An_Assert_Pragma then
                  declare
                     Element      : constant Pragma_Element := Pragmas (Index);
                     Args         : constant Association_List :=
                                      Pragma_Argument_Associations (Element);
                     Arg          : constant Association :=
                                      Argument_By_Name_And_Position
                                        (Args,
                                         Nil_Name,
                                         Check_Position_In_Assert);
                     Expr         : constant Asis.Expression :=
                                      Actual_Parameter (Arg);
                     Column_Start : constant Character_Position_Positive :=
                                      Element_Span (Element).First_Column;
                  begin
                     PP_Assert (Column_Start, Expr);
                  end;
               end if;
            end loop;

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
            PP_Check (Column_Start, Expr);
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

   ---------------------------------
   -- A_Object_Declaration_Pre_Op --
   ---------------------------------

   procedure A_Object_Declaration_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
   begin
      if Cursor_At (Element) < State.Echo_Cursor then
         --  Handling of this Element was already taken care of
         return;
      end if;

      if Flat_Element_Kind (Element) = A_Constant_Declaration then
         declare
            Init_Expr : constant Asis.Expression :=
                                   Initialization_Expression (Element);
         begin
            PP_Echo_Cursor_Range
              (State.Echo_Cursor, Cursor_After (Init_Expr));
            State.Echo_Cursor := Cursor_After (Element);
         end;
      end if;

      declare
         Object_Def : constant Asis.Definition :=
                        Object_Declaration_View (Element);
      begin
         --  If it has a subtype_indication
         if Flat_Element_Kind (Object_Def) = A_Subtype_Indication then
            declare
               Constraint        : constant Asis.Constraint :=
                                     Subtype_Constraint (Object_Def);
               New_Subtype_Name  : constant Wide_String :=
                                     Transform_Subtype_Indication (Object_Def);
               Print_Str1        : constant Wide_String :=
                                     "subtype " & New_Subtype_Name & " is ";
               Decl_Name         : constant Defining_Name_List :=
                                     Asis.Declarations.Names (Element);
               Line              : constant Line_Number_Positive :=
                                     First_Line_Number (Element);
               Column_Start      : constant Character_Position_Positive :=
                                     Element_Span (Element).First_Column;
               Print_Str2        : Unbounded_Wide_String;
            begin
               PP_Echo_Cursor_Range
                 (State.Echo_Cursor, Cursor_Before (Element));

               --  Process multiple definitions : A, B :Integer;
               if Decl_Name'Length = 1 then
                  Print_Str2 := Print_Str2 & Defining_Name_Image
                    (Decl_Name (Decl_Name'First)) & " : ";
               else
                  Print_Str2 := Print_Str2 & Defining_Name_Image
                    (Decl_Name (Decl_Name'First));

                  for J in Decl_Name'First + 1 .. Decl_Name'Last loop
                     Print_Str2 := Print_Str2 & " , " & Defining_Name_Image
                       (Decl_Name (J));
                  end loop;

                  Print_Str2 := Print_Str2 & " : ";
               end if;

               --  Case of an A_Simple_Expression_Range
               if Flat_Element_Kind (Constraint)
                 = A_Simple_Expression_Range
               then
                  PP_Text_At (Line, Column_Start, Print_Str1);

                  Traverse_Element_And_Print (Object_Def);

                  PP_Word (";");

                  Print_Str2 := Print_Str2 &
                  (Trim (New_Subtype_Name, Ada.Strings.Both)) & ";";

                  PP_Text_At (Line, Column_Start, To_Wide_String (
                    Trim ((Print_Str2), Ada.Strings.Both)));

                  --  Case of an An_Index_Constraint
               elsif Flat_Element_Kind (Constraint) = An_Index_Constraint then

                  State.Echo_Cursor := Cursor_After (Element);

                  Transform_An_Index_Constraint (Constraint,
                                                 Print_Str2,
                                                 New_Subtype_Name,
                                                 Control, State);
               end if;

               State.Echo_Cursor := Cursor_After (Element);
            end;
         end if;

         --  If it has an array_type_definition
         if Flat_Element_Kind (Object_Def) =
           A_Constrained_Array_Definition
         then
            declare
               Decl_Name         : constant Defining_Name_List :=
                                     Asis.Declarations.Names (Element);
               Print_Str3     : constant Unbounded_Wide_String  :=
                                  To_Unbounded_Wide_String
                                     (Defining_Name_Image
                                          (Decl_Name (Decl_Name'First)) &
                                      " : " & "array (");
            begin
               PP_Echo_Cursor_Range
                 (State.Echo_Cursor, Cursor_Before (Element));

               State.Echo_Cursor := Cursor_After (Element);

               Transform_Constained_Array_Definition (Object_Def,
                                                      Print_Str3,
                                                      Control, State);
            end;
         end if;
      end;
   end A_Object_Declaration_Pre_Op;

   -------------------------------------------
   -- Transform_An_Index_Constraint --
   -------------------------------------------
   procedure Transform_An_Index_Constraint
     (Element :        Asis.Element;
      Und_String :     Ada.Strings.Wide_Unbounded.Unbounded_Wide_String;
      New_Subtype_Name : Wide_String;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);
   begin
      if Flat_Element_Kind (Element) = An_Index_Constraint then
         declare
            Encl_Element      : constant Asis.Element :=
                                  Enclosing_Element (Element);
            The_Subtype_Name  : constant Asis.Expression :=
                                  Asis.Definitions.Subtype_Mark
                                  (Encl_Element);
            Discrete_Range    : constant Asis.Discrete_Range_List :=
                                  Discrete_Ranges (Element);
            Line              : constant Line_Number_Positive :=
                                  First_Line_Number (Encl_Element);
            Column_Start      : constant Character_Position_Positive :=
                                  Element_Span (Encl_Element).First_Column;
            Tab_Of_Fresh_Name : array (1 .. Discrete_Range'Length) of
                                  Unbounded_Wide_String;
            Last_Fresh_Name   : Unbounded_Wide_String;
            Print_Str3        : Unbounded_Wide_String;
            Print_Str2        : Unbounded_Wide_String  := Und_String;

         begin
            if Discrete_Range'Length = 1 then
               Last_Fresh_Name := To_Unbounded_Wide_String (Fresh_Name);
               PP_Text_At (Line, Column_Start, "subtype " &
                           To_Wide_String (Last_Fresh_Name) &
                           " is Integer range ");

               Traverse_Element_And_Print (Discrete_Range (1));

               PP_Word (";");

               Print_Str3      := Print_Str3 & "subtype " & Last_Fresh_Name &
               " is " & (Trim (Element_Image (The_Subtype_Name),
                 Ada.Strings.Both)) & " (" &
               Trim (New_Subtype_Name, Ada.Strings.Both) & ");";

               PP_Close_Line;

               Print_Str2 := Print_Str2 &
               (Trim (Last_Fresh_Name, Ada.Strings.Both)) & ";";

            else
               Tab_Of_Fresh_Name (1)  := To_Unbounded_Wide_String
                                         (Fresh_Name);

               PP_Text_At (Line, Column_Start, "subtype " &
                           To_Wide_String (Tab_Of_Fresh_Name (1)) &
                           " is Integer range ");

               Traverse_Element_And_Print (Discrete_Range (1));

               PP_Word (";");

               for J in Discrete_Range'First + 1 ..
                 Discrete_Range'Last
               loop

                  Tab_Of_Fresh_Name (J)  :=
                    To_Unbounded_Wide_String
                      (Fresh_Name);

                  PP_Text_At (Line, Column_Start, "subtype " &
                              To_Wide_String
                                (Tab_Of_Fresh_Name (J)) &
                              " is Integer range ");

                  Traverse_Element_And_Print (Discrete_Range (J));

                  PP_Word (";");

                  Last_Fresh_Name := To_Unbounded_Wide_String
                                         (Fresh_Name);
               end loop;

               Print_Str3 := Print_Str3 &
               "subtype " & Last_Fresh_Name & " is " &
               (Trim (Element_Image (The_Subtype_Name),
                  Ada.Strings.Both)) & " (" &
               (Trim (Tab_Of_Fresh_Name (1), Ada.Strings.Both));

               for J in Tab_Of_Fresh_Name'First + 1 ..
                 Tab_Of_Fresh_Name'Last loop

                  Print_Str3 := Print_Str3 & ", " &
                  (Trim (Tab_Of_Fresh_Name (J), Ada.Strings.Both))  &
                  ");";

               end loop;

               PP_Text_At (Line, Column_Start,
                           Trim (To_Wide_String (Print_Str3),
                   Ada.Strings.Both));

               Print_Str2 := Print_Str2 & Last_Fresh_Name & ";";
            end if;

            PP_Text_At (Line, Column_Start, To_Wide_String (
              Trim ((Print_Str2), Ada.Strings.Both)));
         end;

         State.Echo_Cursor := Cursor_After (Element);

      end if;

   end Transform_An_Index_Constraint;

   -------------------------------------------
   -- Transform_Constained_Array_Definition --
   -------------------------------------------
   procedure Transform_Constained_Array_Definition
     (Element :        Asis.Element;
      Und_String :        Unbounded_Wide_String;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);
   begin
      if Flat_Element_Kind (Element) =
        A_Constrained_Array_Definition
      then
         declare
            List_Def       : constant Asis.Definition_List  :=
                               Discrete_Subtype_Definitions (Element);
            Encl_Element   : constant Asis.Element :=
                               Enclosing_Element (Element);
            Line           : constant Line_Number_Positive :=
                               First_Line_Number (Encl_Element);
            Column_Start   : constant Character_Position_Positive :=
                               Element_Span (Encl_Element).First_Column;
            Array_Comp_Def : constant Asis.Component_Definition :=
                               Array_Component_Definition (Element);
            Array_Comp_Sub : constant Asis.Definition :=
                               Component_Definition_View (Array_Comp_Def);
            Print_Str3     : Unbounded_Wide_String  := Und_String;
         begin
            PP_Echo_Cursor_Range
              (State.Echo_Cursor, Cursor_Before (Element));

            --  Case of alone discrete subtype definition
            if List_Def'Length = 1 then
               declare
                  New_Subtype_Name1 : constant Wide_String :=
                                        Transform_Subtype_Indication
                      (List_Def (1));

                  Print_Str1   : constant Wide_String := "subtype " &
                  New_Subtype_Name1 & " is ";

               begin
                  Print_Str3 := Print_Str3 & New_Subtype_Name1;

                  --  A_Discrete_Subtype_Indication_As_Subtype_Definition
                  if Flat_Element_Kind (List_Def (1)) =
                    A_Subtype_Indication
                    or
                      Flat_Element_Kind (List_Def (1)) =
                    A_Discrete_Subtype_Indication_As_Subtype_Definition
                  then
                     if not (Is_Nil (Subtype_Constraint
                                     (List_Def (1)))) then

                        State.Echo_Cursor := Cursor_Before (Element);

                        PP_Text_At (Line, Column_Start, Print_Str1);

                        Traverse_Element_And_Print (List_Def (1));

                        PP_Word (";");

                     end if;
                  end if;

                  --  A_Discrete_Subtype_Indication_As_Subtype_Definition
                  if Flat_Element_Kind (List_Def (1)) =
                    A_Discrete_Simple_Expression_Range_As_Subtype_Definition
                  then
                     declare
                        Lower_Expr : constant Asis.Expression :=
                          Lower_Bound (List_Def (1));
                     begin
                        if Flat_Element_Kind (Lower_Expr) =
                          An_Integer_Literal then

                           PP_Text_At (Line, Column_Start, "subtype " &
                                       Fresh_Name
                                       & " is Integer range ");

                           Traverse_Element_And_Print (List_Def (1));

                           PP_Word (";");

                        end if;
                     end;
                  end if;
               end;

            --  Case of multiple discretes subtype definition
            else
               declare
                  New_Subtype_Name1 : constant Wide_String :=
                                        Transform_Subtype_Indication
                                        (List_Def (1));
                  Print_Str1        : constant Wide_String := "subtype " &
                                        New_Subtype_Name1 & " is ";
               begin
                  Print_Str3 := Print_Str3 & New_Subtype_Name1;

                  for J in List_Def'First + 1 .. List_Def'Last loop
                     if Flat_Element_Kind (List_Def (J)) =
                       A_Subtype_Indication
                       or
                         Flat_Element_Kind (List_Def (J)) =
                       A_Discrete_Subtype_Indication_As_Subtype_Definition
                     then
                        if not (Is_Nil (Subtype_Constraint
                                        (List_Def (J)))) then

                           PP_Text_At (Line, Column_Start, Print_Str1);
                           Traverse_Element_And_Print
                             (List_Def (J));

                           PP_Word (";");

                        end if;

                        Print_Str3 := Print_Str3  &  ","
                          & New_Subtype_Name1;

                     end if;

                     if Flat_Element_Kind (List_Def (J)) =
                       A_Discrete_Simple_Expression_Range_As_Subtype_Definition
                     then
                        declare
                           Lower_Expr : constant Asis.Expression :=
                                          Lower_Bound (List_Def (J));
                        begin
                           if Flat_Element_Kind (Lower_Expr) =
                             An_Integer_Literal then
                              PP_Text_At (Line, Column_Start, "subtype " &
                                          Fresh_Name
                                          & " is Integer range ");

                              Traverse_Element_And_Print
                                (List_Def (J));

                              PP_Word (";");
                           end if;

                           Print_Str3 := Print_Str3  &  ","
                             & New_Subtype_Name1;
                        end;
                     end if;
                  end loop;
               end;
            end if;

            --  Process the array component
            if Flat_Element_Kind (Array_Comp_Sub) =
              A_Subtype_Indication then
               declare
                  New_Subtype_Name2 : constant Wide_String :=
                                          Transform_Subtype_Indication (
                                          Array_Comp_Sub);
                  Print_Str2        : constant Wide_String := "subtype " &
                                        New_Subtype_Name2 & " is " &
                                        Trim (Element_Image (Array_Comp_Sub),
                                        Ada.Strings.Both);
               begin
                  if not (Is_Nil (Subtype_Constraint (Array_Comp_Sub))) then

                     PP_Text_At (Line, Column_Start, Print_Str2);
                     PP_Word (";");

                  end if;
                  Print_Str3 := Print_Str3 & ") of " & New_Subtype_Name2;

                  PP_Text_At (Line, Column_Start,
                              To_Wide_String (Print_Str3));

                  State.Echo_Cursor := Cursor_After (Element);
               end;
            end if;
         end;
      end if;

   end Transform_Constained_Array_Definition;

   -------------------------------
   -- A_Type_Declaration_Pre_Op --
   -------------------------------
   procedure A_Type_Declaration_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
   begin
      declare
         Type_Def : constant Asis.Definition :=
           Type_Declaration_View (Element);
      begin
         --  Array Definition kinds
         if Flat_Element_Kind (Type_Def) =
           A_Constrained_Array_Definition
         then
            declare
               Decl_Name  : constant Defining_Name_List :=
                 Asis.Declarations.Names (Element);
               Print_Str3 : constant Unbounded_Wide_String  :=
                                  To_Unbounded_Wide_String
                                     ("type " & Defining_Name_Image
                                              (Decl_Name (Decl_Name'First))
                                      & " is array (");

            begin
               PP_Echo_Cursor_Range
                 (State.Echo_Cursor, Cursor_Before (Element));

               State.Echo_Cursor := Cursor_After (Element);

               Transform_Constained_Array_Definition (Type_Def,
                                                      Print_Str3,
                                                      Control, State);
            end;
         end if;

         --  Record Definition kinds
         if Flat_Element_Kind (Type_Def) = A_Record_Type_Definition then
            declare
               Record_Def        : constant Asis.Definition :=
                                     Asis.Definitions.Record_Definition
                                       (Type_Def);
               Record_Comp_List  : constant Asis.Record_Component_List :=
                                     Record_Components (Record_Def);
               Decl_Name         : constant Defining_Name_List :=
                                     Asis.Declarations.Names (Element);
               pragma Assert (Decl_Name'Length = 1);
               Line              : constant Line_Number_Positive :=
                                     First_Line_Number (Element);
               Column_Start      : constant Character_Position_Positive :=
                                     Element_Span (Element).First_Column;
               Tab_Of_Fresh_Name : array (1 .. Record_Comp_List'Length)
                                     of Unbounded_Wide_String;

            begin
               PP_Echo_Cursor_Range
                 (State.Echo_Cursor, Cursor_Before (Element));

               for Record_Comp in Record_Comp_List'Range loop
                  declare
                     Component_Decl : constant Asis.Declaration :=
                                        Component_Declaration
                                          (Record_Comp_List (Record_Comp));
                     Object_Def     : constant Asis.Definition :=
                                        Object_Declaration_View
                                         (Component_Decl);
                     Component_View : constant Asis.Component_Definition :=
                                        Component_Definition_View
                                        (Object_Def);
                     Constraint     : constant Asis.Constraint :=
                                        Subtype_Constraint (Component_View);
                     New_Subtype_Name1   : constant Wide_String :=
                                        Transform_Subtype_Indication
                                          (Component_View);
                     Print_Str1     : constant Wide_String :=
                       "subtype " & New_Subtype_Name1 & " is " &
                                           Trim (Element_Image
                                                 (Component_View),
                                                  Ada.Strings.Left) & ";";
                  begin
                     if Flat_Element_Kind (Component_View)
                       = A_Subtype_Indication then

                        Tab_Of_Fresh_Name (Record_Comp) :=
                          To_Unbounded_Wide_String (New_Subtype_Name1);

                        if Flat_Element_Kind (Constraint)
                          = A_Simple_Expression_Range
                        then
                           PP_Text_At (Line, Column_Start, Print_Str1);

                           --  Case of an An_Index_Constraint
                        elsif Flat_Element_Kind (Constraint)
                          = An_Index_Constraint then

                           Transform_An_Index_Constraint (Constraint,
                                                   To_Unbounded_Wide_String
                                                            (Print_Str1),
                                                         New_Subtype_Name1,
                                                          Control, State);
                        end if;
                     end if;
                  end;
               end loop;

               PP_Text_At (Line, Column_Start, "type " & Defining_Name_Image
                           (Decl_Name (Decl_Name'First))
                           & " is record ");

               for J in Tab_Of_Fresh_Name'Range loop
                  declare
                     Component_Decl : constant Asis.Declaration :=
                                        Component_Declaration
                                          (Record_Comp_List (J));
                     Object_Def     : constant Asis.Definition :=
                                        Object_Declaration_View
                                        (Component_Decl);
                     Component_View : constant Asis.Component_Definition :=
                                        Component_Definition_View (Object_Def);
                     Constraint     : constant Asis.Constraint :=
                                        Subtype_Constraint (Component_View);
                     Decl_Name      : constant Defining_Name_List :=
                                        Asis.Declarations.Names
                                           (Component_Decl);
                     pragma Assert (Decl_Name'Length = 1);
                     Print_Str2     : constant Wide_String :=
                                        Defining_Name_Image
                                        (Decl_Name (Decl_Name'First)) & " : "
                                        & (To_Wide_String (
                                        Tab_Of_Fresh_Name (J))) & ";";
                     pragma Assert (Decl_Name'Length = 1);
                     Line            : constant Line_Number_Positive :=
                       First_Line_Number (Component_View);
                     Column_Start    : constant Character_Position_Positive :=
                       Element_Span (Component_View).First_Column;
                  begin
                     if Flat_Element_Kind (Component_View)
                       = A_Subtype_Indication then

                        if Flat_Element_Kind (Constraint)
                          = A_Simple_Expression_Range
                        then
                           PP_Text_At (Line, Column_Start, Print_Str2);
                           State.Echo_Cursor := Cursor_After (Element);

                        elsif Flat_Element_Kind (Constraint)
                          = An_Index_Constraint
                        then
                           PP_Text_At (Line, Column_Start, Print_Str2);

                        else

                           PP_Text_At (Line, Column_Start, Print_Str2);
                           State.Echo_Cursor := Cursor_After (Element);
                        end if;
                     end if;
                  end;
               end loop;

               PP_Text_At (Line, Column_Start, "end record;");

            end;
         end if;
      end;
   end A_Type_Declaration_Pre_Op;

   procedure A_Discrete_Subtype_Definition_Pre_Op
     (Element :        Asis.Element;
      Control : in out Traverse_Control;
      State   : in out Source_Traversal_State)
   is
      pragma Unreferenced (Control);
   begin
      declare
         Encl_Element : constant Asis.Element := Enclosing_Element (Element);
         Print_Str1     : Unbounded_Wide_String;
      begin
         PP_Echo_Cursor_Range (State.Echo_Cursor,
                               Cursor_Before (Encl_Element));

         if Flat_Element_Kind (Element) =
           A_Discrete_Simple_Expression_Range_As_Subtype_Definition then
            declare
               Lower_Expr : constant Asis.Expression :=
                 Lower_Bound (Element);
               Var_Name : constant Wide_String := Fresh_Name;
            begin
               if Flat_Element_Kind (Lower_Expr) =
                 An_Integer_Literal then
                  Print_Str1 := Print_Str1 & "subtype " &
                   Var_Name & " Integer range ";
                  PP_Word (To_Wide_String (Print_Str1));
                  State.Echo_Cursor := Cursor_At (Element);
               end if;
               Reach_Element_And_Traverse
                 (Element, State);
            end;
         end if;
      end;
   end A_Discrete_Subtype_Definition_Pre_Op;

end Sparkify.Pre_Operations;
