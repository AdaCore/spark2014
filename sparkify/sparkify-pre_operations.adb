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

with Asis.Compilation_Units;           use Asis.Compilation_Units;
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

   procedure Reach_Element_And_Traverse
     (Element : Asis.Element;
      State   : in out Source_Traversal_State);
   --  Echo everything before Element; then, traverse it in Printing_Code
   --  mode (prefixing identifiers et cetera). At the end of procedure,
   --  the cursor is set after Element.

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
         --  The iteration scheme can contain identifiers; they
         --  should be prefixed if needed. To do so, we should do
         --  Traverse_Source on what's before the first statement.
         Reach_Element_And_Traverse (Get_Iteration_Scheme (Element), State);
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
            Args : constant Association_List :=
              Pragma_Argument_Associations (Element);
            Arg  : constant Association := Argument_By_Name_And_Position
              (Args, Nil_Name, Check_Position_In_Assert);
            Expr : constant Asis.Expression := Actual_Parameter (Arg);
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

      function Is_Defined_In_Standard_Or_Current_Compilation_Unit
        (Element : Asis.Element) return Boolean;

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

      function Prepend_Package_Name
        (Element : Asis.Element;
         Name    : Wide_String) return Wide_String;

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
               Names : constant Defining_Name_List :=
                 Asis.Declarations.Names (Encl_Element);
               pragma Assert (Names'Length = 1);
               Expanded_Name : constant Wide_String :=
                 Defining_Name_Image (Names (Names'First)) & "." & Name;
            begin
               return Prepend_Package_Name (Encl_Element, Expanded_Name);
            end;
         else
            return Name;
         end if;
      end Prepend_Package_Name;
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

   --------------------------------
   -- Reach_Element_And_Traverse --
   --------------------------------

   procedure Reach_Element_And_Traverse
     (Element : Asis.Element;
      State   : in out Source_Traversal_State)
   is
      Source_Control : Asis.Traverse_Control  := Asis.Continue;
      Source_State   : Source_Traversal_State := Initial_State;
   begin
      PP_Echo_Cursor_Range (State.Echo_Cursor, Cursor_Before (Element));
      Source_State.Echo_Cursor := Cursor_At (Element);
      Traverse_Source (Element, Source_Control, Source_State);
      PP_Echo_Cursor_Range (Source_State.Echo_Cursor,
                            Cursor_At_End_Of (Element));
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
                 Defining_Name_Image (Decl_Name (Decl_Name'First)) & "'";
            begin
               PP_Echo_Cursor_Range
                 (State.Echo_Cursor, Cursor_Before (Element));
               PP_Word (Type_Str);
               State.Echo_Cursor := Cursor_At (Element);
            end;
         end if;
      end;

   end An_Aggregate_Pre_Op;

end Sparkify.Pre_Operations;
