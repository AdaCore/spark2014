------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       A L F A . D E F I N I T I O N                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2011, AdaCore                       --
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

with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Text_IO;           use Ada.Text_IO;

with AA_Util;               use AA_Util;
with Alloc;                 use Alloc;
with Atree;                 use Atree;
with Debug;
with Einfo;                 use Einfo;
with Errout;                use Errout;
with Lib;                   use Lib;
with Namet;                 use Namet;
with Nlists;                use Nlists;
with Snames;                use Snames;
with Sem_Eval;              use Sem_Eval;
with Sinfo;                 use Sinfo;
with Sinput;                use Sinput;
with Stand;                 use Stand;
with Table;

with Alfa.Frame_Conditions; use Alfa.Frame_Conditions;
with Alfa.Common; use Alfa.Common;

with Alfa_Violations; use all type Alfa_Violations.Vkind;

package body Alfa.Definition is

   Output_File : Ada.Text_IO.File_Type;
   --  <file>.alfa in which this pass generates information about subprograms
   --  in Alfa and subprograms not in Alfa.

   ---------------------
   -- Local Constants --
   ---------------------

   --  Standard types which are in Alfa are associated to True

   Standard_Type_Is_In_Alfa : constant array (S_Types) of Boolean :=
     (S_Boolean             => True,

      S_Short_Short_Integer => True,
      S_Short_Integer       => True,
      S_Integer             => True,
      S_Long_Integer        => True,
      S_Long_Long_Integer   => True,

      S_Natural             => True,
      S_Positive            => True,

      S_Short_Float         => False,
      S_Float               => False,
      S_Long_Float          => False,
      S_Long_Long_Float     => False,

      S_Character           => True,
      S_Wide_Character      => True,
      S_Wide_Wide_Character => True,

      S_String              => True,
      S_Wide_String         => False,
      S_Wide_Wide_String    => False,

      S_Duration            => False);

   ------------------
   -- Global State --
   ------------------

   Current_Unit_Is_Main_Body : Boolean;
   Current_Unit_Is_Main_Spec : Boolean;

   Inside_Expression_With_Actions : Boolean := False;
   --  True during the analysis of an expression-with-actions

   All_Types : Id_Set.Set;
   --  Set of all types whose declaration has been analyzed so far

   procedure Mark_Type_Declaration (Id : Unique_Entity_Id);
   --  Should be called on every type declaration. Add Id to All_Types.

   function Type_Entity_Marked (Id : Unique_Entity_Id) return Boolean;
   --  Return whether the declaration for Id was analyzed so far

   function Is_Main_Cunit (N : Node_Id) return Boolean is
     (Get_Cunit_Unit_Number (Parent (N)) = Main_Unit);

   function Is_Spec_Unit_Of_Main_Unit (N : Node_Id) return Boolean is
     (Present (Corresponding_Body (N))
       and then Is_Main_Cunit
         (Unit (Enclosing_Lib_Unit_Node (Corresponding_Body (N)))));

   function Is_In_Standard_Package (N : Node_Id) return Boolean is
      (Sloc (N) = Standard_Location);

   function In_Main_Unit_Body (N : Node_Id) return Boolean;
   function In_Main_Unit_Spec (N : Node_Id) return Boolean;

   ------------------------------------------------
   -- Pragma Annotate (GNATprove, Force/Disable) --
   ------------------------------------------------

   Formal_Proof_On  : Id_Set.Set;
   Formal_Proof_Off : Id_Set.Set;

   function Formal_Proof_Currently_Disabled return Boolean;
   --  Determine the most top-level scope to have formal proof forced or
   --  disabled, and return True if formal proof is disabled. Return False in
   --  all other cases.

   function Formal_Proof_Currently_Forced return Boolean;
   --  Determine the most top-level scope to have formal proof forced or
   --  disabled, and return True if formal proof is forced. Return False in all
   --  other cases. This is useful to notify the user about Alfa violations in
   --  a scope where formal proof is forced.

   function Force_Alfa (N : Node_Id) return Boolean is
     ((Debug.Debug_Flag_Dot_EE
        and then (In_Main_Unit_Spec (N)
                   or else In_Main_Unit_Body (N)))
       or else
         Formal_Proof_Currently_Forced);
   --  Return whether Alfa rules should be enforced in the current scope,
   --  either because option -gnatd.E was passed to gnat2why (which only
   --  applies to user source code), or because the current scope is forcing
   --  formal proof.

   ----------------
   -- Alfa Marks --
   ----------------

   type Violations is array (Alfa_Violations.Vkind) of Id_Set.Set;

   Spec_Violations : Violations;
   --  Sets of entities which violate Alfa restrictions, per violation kind

   Body_Violations : Violations;
   --  Sets of subprogram entities whose body violate Alfa restrictions, per
   --  violation kind.

   Standard_In_Alfa : Id_Set.Set;
   --  Entities from package Standard which are in Alfa

   Specs_In_Alfa    : Id_Set.Set;
   --  Subprogram entities whose spec is in Alfa

   Bodies_In_Alfa   : Id_Set.Set;
   --  Subprogram entities whose body is in Alfa

   Types_In_Alfa    : Id_Set.Set;
   --  Type entities in Alfa

   Objects_In_Alfa  : Id_Set.Set;
   --  Object entities in Alfa

   function "+" (E : Unique_Entity_Id) return Entity_Id is (Entity_Id (E));
   --  Safe conversion from unique entity to entity

   function Complete_Error_Msg
     (Msg : String;
      V   : Alfa_Violations.Vkind) return String;
   --  Generate an error message for Not_In_Roadmap violations, and a warning
   --  message for Not_Yet_Implemented violations.

   procedure Inherit_Violations
     (A        : in out Violations;
      To, From : Unique_Entity_Id);

   function Standard_Is_In_Alfa (Id : Unique_Entity_Id) return Boolean is
      (Standard_In_Alfa.Contains (+Id));

   function Body_Is_Computed_In_Alfa (Id : Unique_Entity_Id) return Boolean;
   --  Return whether a violation of Alfa was detected while analyzing the body
   --  of subprogram Id.

   function Object_Is_Computed_In_Alfa (Id : Unique_Entity_Id) return Boolean;
   --  Return whether a violation of Alfa was detected while analyzing the
   --  definition of object Id.

   function Spec_Is_Computed_In_Alfa (Id : Unique_Entity_Id) return Boolean;
   --  Return whether a violation of Alfa was detected while analyzing the spec
   --  of subprogram Id.

   function Type_Is_Computed_In_Alfa (Id : Unique_Entity_Id) return Boolean;
   --  Return whether a violation of Alfa was detected while analyzing the
   --  definition of type Id.

   procedure Filter_In_Alfa (N : Node_Id; Kind : Alfa_Decl);
   --  Helper procedure for marking procedures below

   procedure Mark_Body_In_Alfa (Id : Unique_Entity_Id; N : Node_Id);
   --  Mark subprogram body Id as being in Alfa

   procedure Mark_Object_In_Alfa
     (Id      : Unique_Entity_Id;
      N       : Node_Id;
      In_Alfa : Boolean);
   --  Mark object Id as being in Alfa if In_Alfa is set, or not being in Alfa
   --  otherwise.

   procedure Mark_Spec_In_Alfa (Id : Unique_Entity_Id; N : Node_Id);
   --  Mark subprogram spec Id as being in Alfa. Note that Id can be really
   --  either a subprogram spec, or a subprogram body serving as its own spec.

   procedure Mark_Type_In_Alfa
     (Id      : Unique_Entity_Id;
      In_Alfa : Boolean);
   --  Mark type Id as being in Alfa if In_Alfa is set, or not being in Alfa
   --  otherwise.

   function Body_Is_In_Alfa (Id : Unique_Entity_Id) return Boolean;
   --  Return whether the body of subprogram Id is in Alfa

   function Object_Is_In_Alfa (Id : Unique_Entity_Id) return Boolean;
   --  Return whether an object Id is in Alfa

   function Spec_Is_In_Alfa (Id : Unique_Entity_Id) return Boolean;
   --  Return whether the spec of subprogram Id is in Alfa

   function Type_Is_In_Alfa (Ent : Entity_Id) return Boolean;
   --  Return whether a type Ent is in Alfa. Contrary to other .._Is_In_Alfa
   --  functions, it takes an entity rather than a unique entity. Indeed,
   --  private types are always in Alfa, even when the corresponding full type
   --  is not in Alfa. This corresponds to cases where a client of the package,
   --  which has only view over the private declaration, may still be in Alfa,
   --  while an operation in the package over non-Alfa fields may not be in
   --  Alfa.

   procedure Generate_Output_In_Out_Alfa (Id : Unique_Entity_Id);
   --  Produce a line in output file for subprogram Id, following syntax:
   --
   --    cd name location opt_list_NIR opt_list_NYI
   --
   --  where
   --
   --    c and d are characters which denote respectively whether the body and
   --    spec of subprogram Id are:
   --      + in Alfa
   --      - not in Alfa roadmap
   --      * not yet implemented in Alfa
   --
   --    name is the name of subprogram Id
   --    location is the location (file:line) of subprogram Id
   --
   --    opt_list_NIR and opt_list_NYI are optional lists of violations of Alfa
   --    for not-in-roadmap constructs (NIR) or not-yet-implemented constructs
   --    (NYI). opt_list_NIR is enclosed in parentheses. opt_list_NYI is
   --    enclosed in brackets. Both are comma-separated lists.
   --
   --  examples:
   --
   --  -+ pack__f f.adb:3 (tasking)
   --  Subprogram Pack.F has its spec in Alfa, and its body not in Alfa, due to
   --  the use of tasking.
   --
   --  ++ pack__g f.adb:78
   --  Subprogram Pack.G is in Alfa
   --
   --  ** pack__h f.adb:3 [slice, not yet implemented]
   --  Subprogram Pack.H has both its spec and body not implemented in Alfa,
   --  due to the use of slices, plus some other not precised constructs.

   -----------------
   -- Scope Stack --
   -----------------

   --  A stack of scopes records scopes currently open. The entity referenced
   --  can be:
   --    . a package spec
   --    . a package body
   --    . a subprogram spec (even when treating the subprogram body)
   --    . a variable (when treating initializing expression)
   --    . a type (when treating a type declaration)

   --  Is_Logic is True for assertions, pre- and postconditions
   type Scope_Record (Is_Logic : Boolean := False) is record
      case Is_Logic is
         when False =>
            Entity  : Unique_Entity_Id;
            Is_Body : Boolean;  --  True for a package/subprogram body
         when True =>
            null;
      end case;
   end record;

   First_Scope_Index : constant := 0;

   package Scope_Stack is new Table.Table (
     Table_Component_Type => Scope_Record,
     Table_Index_Type     => Int,
     Table_Low_Bound      => First_Scope_Index,
     Table_Initial        => Alloc.Scope_Stack_Initial,
     Table_Increment      => Alloc.Scope_Stack_Increment,
     Table_Name           => "Alfa.Definition.Scope_Stack");

   function Current_Scope return Scope_Record;
   --  Return the top-most scope that is not null

   function In_Logic_Scope return Boolean is
     (for some S in First_Scope_Index .. Scope_Stack.Last =>
        Scope_Stack.Table (S).Is_Logic);
   --  Return True if there is a logic scope in the current scope stack

   procedure Pop_Scope (E : Unique_Entity_Id);
   --  Remove the top scope in the stack, which should match with entity E

   procedure Push_Scope
     (E       : Unique_Entity_Id;
      Is_Body : Boolean := False);

   --  Set entity S as the top scope in the stack

   procedure Push_Logic_Scope;
   --  Push a logic scope as the top scope in the stack

   procedure Pop_Logic_Scope;
   --  Remove the top scope in the stack, which should be a logic scope

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Safe_Instantiation_Depth (Id : Unique_Entity_Id) return Int;
   --  Compute the instantiation Depth of Id

   procedure Mark (N : Node_Id);
   --  Generic procedure for marking code as in Alfa / not in Alfa

   procedure Mark_List (L : List_Id);
   --  Call Mark on all nodes in list L

   procedure Mark_Non_Alfa
     (Msg    : String;
      N      : Node_Id;
      V      : Alfa_Violations.Vkind;
      Silent : Boolean        := False);
   --  Mark the current subprogram containing node N (if any) as not being in
   --  Alfa. If the corresponding scope is a spec, then mark the subprogram
   --  specification as not in Alfa. Otherwise, mark the subprogram body as not
   --  in Alfa.
   --
   --  Indeed, this procedure may be called during the analysis of a
   --  precondition or postcondition, or during the analysis of a subprogram's
   --  body. In the first case, the specification of the current subprogram
   --  must be marked as not being in Alfa, as the contract is considered to be
   --  part of the specification, so that calls to this subprogram are not in
   --  Alfa. In the second case, mark the body as not being in Alfa, which does
   --  not prevent the subprogram's specification, and calls to the subprogram,
   --  from being in Alfa.
   --
   --  If the subprogram being marked as not in Alfa is annotated with
   --  formal proof forced, then an error is issued with message Msg on node N,
   --  unless Silent is True.

   procedure Mark_Non_Alfa
     (Msg  : String;
      N    : Node_Id;
      From : Unique_Entity_Id);
   --  Similar to Mark_Non_Alfa taking a Alfa_Violations.Vkind as parameter,
   --  except here violations are inherited from entity From.

   procedure Mark_Non_Alfa_Declaration
     (Msg    : String;
      N      : Node_Id;
      V      : Alfa_Violations.Vkind;
      Silent : Boolean        := False);
   --  Mark the declaration N as not being in Alfa, as well as the enclosing
   --  subprogram if any. If Silent is True, then never issue an error message,
   --  even if formal proof is forced.

   procedure Mark_Non_Alfa_Declaration
     (Msg  : String;
      N    : Node_Id;
      From : Unique_Entity_Id);
   --  Similar to Mark_Non_Alfa_Declaration taking a Alfa_Violations.Vkind as
   --  parameter, except here violations are inherited from entity From.

   generic
      with procedure Mark_Body_Violations (E : Unique_Entity_Id) is <>;
      with procedure Mark_Spec_Violations (E : Unique_Entity_Id) is <>;
   procedure Mark_Violations (Scop : Scope_Record);
   --  Helper procedure called in Mark_Non_Alfa

   generic
      with procedure Mark_Body_Violations (E : Unique_Entity_Id) is <>;
      with procedure Mark_Spec_Violations (E : Unique_Entity_Id) is <>;
   procedure Mark_Violations_For_All_Scopes;
   --  Helper procedure called in Mark_Non_Alfa

   --  Special treatment for marking some kinds of nodes

   procedure Mark_Type_Entity                 (Id : Unique_Entity_Id);
   --  Types are special, we represent them by entities.

   procedure Mark_Attribute_Reference         (N : Node_Id);
   procedure Mark_Binary_Op                   (N : Node_Id);
   procedure Mark_Call                        (N : Node_Id);
   procedure Mark_Component_Declaration       (N : Node_Id);
   procedure Mark_Conditional_Expression      (N : Node_Id);
   procedure Mark_Function_Specification      (N : Node_Id);
   procedure Mark_Handled_Statements          (N : Node_Id);
   procedure Mark_Identifier_Or_Expanded_Name (N : Node_Id);
   procedure Mark_If_Statement                (N : Node_Id);
   procedure Mark_Iteration_Scheme            (N : Node_Id);
   procedure Mark_Object_Declaration          (N : Node_Id);
   procedure Mark_Object_Renaming_Declaration (N : Node_Id);
   procedure Mark_Package_Body                (N : Node_Id);
   procedure Mark_Package_Declaration         (N : Node_Id);
   procedure Mark_Package_Specification       (N : Node_Id);
   procedure Mark_Pragma                      (N : Node_Id);
   procedure Mark_Simple_Return_Statement     (N : Node_Id);
   procedure Mark_Subprogram_Body             (N : Node_Id);
   procedure Mark_Subprogram_Declaration      (N : Node_Id);
   procedure Mark_Subprogram_Specification    (N : Node_Id);
   procedure Mark_Subtype_Indication          (N : Node_Id);
   procedure Mark_Type_Conversion             (N : Node_Id);
   procedure Mark_Type_Definition             (Id : Unique_Entity_Id);
   procedure Mark_Unary_Op                    (N : Node_Id);

   ------------------------------
   -- Alfa marking of entities --
   ------------------------------

   function Body_Is_Computed_In_Alfa (Id : Unique_Entity_Id) return Boolean is
     (for all S of Body_Violations => not S.Contains (+Id));

   function Object_Is_Computed_In_Alfa
     (Id : Unique_Entity_Id) return Boolean
   is
     (for all S of Spec_Violations => not S.Contains (+Id));

   function Spec_Is_Computed_In_Alfa (Id : Unique_Entity_Id) return Boolean is
     (for all S of Spec_Violations => not S.Contains (+Id));

   function Type_Is_Computed_In_Alfa (Id : Unique_Entity_Id) return Boolean is
     (for all S of Spec_Violations => not S.Contains (+Id));

   procedure Filter_In_Alfa (N : Node_Id; Kind : Alfa_Decl) is
   begin
      if Current_Unit_Is_Main_Spec then
         Decls_In_Spec (Kind).Append (N);
      elsif Current_Unit_Is_Main_Body then
         Decls_In_Body (Kind).Append (N);
      end if;
   end Filter_In_Alfa;

   procedure Mark_Body_In_Alfa (Id : Unique_Entity_Id; N : Node_Id) is
   begin
      Bodies_In_Alfa.Include (+Id);
      Filter_In_Alfa (N, Alfa_Subprogram_Body);
   end Mark_Body_In_Alfa;

   procedure Mark_Object_In_Alfa
     (Id      : Unique_Entity_Id;
      N       : Node_Id;
      In_Alfa : Boolean) is
   begin
      if In_Alfa then
         Objects_In_Alfa.Include (+Id);
      end if;

      --  Declarations of objects inside expression with actions are translated
      --  specially into let-expressions.

      if not Inside_Expression_With_Actions

        --  This is not sufficient currently as some temporaries are
        --  introduced at statement level. HACK until this is cleaned up.

        and then (Comes_From_Source (Original_Node (N))
                   or else Is_Package_Level_Entity (+Id))
      then
         if In_Alfa then
            Filter_In_Alfa (N, Alfa_Object);
         else
            Filter_In_Alfa (+Id, Non_Alfa_Object);
         end if;
      end if;
   end Mark_Object_In_Alfa;

   procedure Mark_Spec_In_Alfa (Id : Unique_Entity_Id; N : Node_Id) is
   begin
      Specs_In_Alfa.Include (+Id);
      Filter_In_Alfa (N, Alfa_Subprogram_Spec);
   end Mark_Spec_In_Alfa;

   procedure Mark_Type_In_Alfa
     (Id      : Unique_Entity_Id;
      In_Alfa : Boolean)
   is
      Alfa_Status : constant Alfa_Decl :=
         (if In_Alfa then Alfa_Type else Non_Alfa_Type);

   begin
      if In_Alfa then
         Types_In_Alfa.Include (+Id);
      end if;

      if not Type_Entity_Marked (+Id)
        and then not Is_In_Standard_Package (+Id)
      then
         Filter_In_Alfa (+Id, Alfa_Status);
      end if;
   end Mark_Type_In_Alfa;

   function Body_Is_In_Alfa (Id : Unique_Entity_Id) return Boolean is
     (Id_Set.Contains (Bodies_In_Alfa, +Id));

   function Object_Is_In_Alfa (Id : Unique_Entity_Id) return Boolean is
   begin
      if Scope (+Id) = Standard_Standard then
         return Standard_In_Alfa.Contains (+Id);
      else
         return (Id_Set.Contains (Objects_In_Alfa, +Id));
      end if;
   end Object_Is_In_Alfa;

   function Spec_Is_In_Alfa (Id : Unique_Entity_Id) return Boolean is
     (Id_Set.Contains (Specs_In_Alfa, +Id));

   function Type_Is_In_Alfa (Ent : Entity_Id) return Boolean is
      Id : constant Unique_Entity_Id := Unique (Ent);

   begin
      if Ekind (Ent) in Private_Kind
        and then Ekind (Ent) not in Record_Kind
      then
         return True;
      end if;

      if Scope (+Id) = Standard_Standard then
         return Standard_In_Alfa.Contains (+Id);
      end if;

      --  Type might not have been marked yet, in case it is an Itype or a
      --  class-wide type.

      if not Type_Entity_Marked (+Id) then
         Mark (+Id);
      end if;

      return Id_Set.Contains (Types_In_Alfa, +Id);
   end Type_Is_In_Alfa;

   procedure Mark_Type_Declaration (Id : Unique_Entity_Id) is
   begin
      All_Types.Include (+Id);
   end Mark_Type_Declaration;

   function Type_Entity_Marked (Id : Unique_Entity_Id) return Boolean is
     (All_Types.Contains (+Id));

   ----------------------------
   -- Close_Alfa_Output_File --
   ----------------------------

   procedure Close_Alfa_Output_File is
   begin
      Close (Output_File);
   end Close_Alfa_Output_File;

   ------------------------
   -- Complete_Error_Msg --
   ------------------------

   function Complete_Error_Msg
     (Msg : String;
      V   : Alfa_Violations.Vkind) return String is
   begin
      case V is
         when Alfa_Violations.Not_In_Roadmap =>
            return Msg & " is not in Alfa";
         when Alfa_Violations.Not_Yet_Implemented =>
            return Msg & "? is not yet implemented in Alfa";
      end case;
   end Complete_Error_Msg;

   -------------------
   -- Current_Scope --
   -------------------

   function Current_Scope return Scope_Record is
     (Scope_Stack.Table (Scope_Stack.Last));

   -------------------------------------
   -- Formal_Proof_Currently_Disabled --
   -------------------------------------

   function Formal_Proof_Currently_Disabled return Boolean is
   begin
      for Idx in reverse Scope_Stack.First .. Scope_Stack.Last loop
         declare
            E : constant Unique_Entity_Id := Scope_Stack.Table (Idx).Entity;
         begin
            if Formal_Proof_Off.Contains (+E) then
               return True;
            elsif Formal_Proof_On.Contains (+E) then
               return False;
            end if;
         end;
      end loop;
      return False;
   end Formal_Proof_Currently_Disabled;

   -----------------------------------
   -- Formal_Proof_Currently_Forced --
   -----------------------------------

   function Formal_Proof_Currently_Forced return Boolean is
   begin
      for Idx in reverse Scope_Stack.First .. Scope_Stack.Last loop
         if not Scope_Stack.Table (Idx).Is_Logic then
            declare
               E : constant Unique_Entity_Id := Scope_Stack.Table (Idx).Entity;
            begin
               if Formal_Proof_On.Contains (+E) then
                  return True;
               elsif Formal_Proof_Off.Contains (+E) then
                  return False;
               end if;
            end;
         end if;
      end loop;
      return False;
   end Formal_Proof_Currently_Forced;

   ---------------------------------
   -- Generate_Output_In_Out_Alfa --
   ---------------------------------

   procedure Generate_Output_In_Out_Alfa (Id : Unique_Entity_Id) is
      generic
         type Violation_Subkind is (<>);
         Open, Close : Character;
         with function Has_Violation
           (V : Violation_Subkind;
            E : Unique_Entity_Id) return Boolean is <>;
         with function Get_Violation_Msg
           (V : Violation_Subkind) return Unbounded_String is <>;
      function Collect_Msg_Violations
        (E : Unique_Entity_Id) return String;
      --  Produce a comma-separated list of message for NYI or NIR violations,
      --  enclosed in Open-Close characters.

      function Suffix return String;
      --  Suffix string indicates why subprogram body is not in Alfa

      ----------------------
      -- Helper Functions --
      ----------------------

      function Has_Violation
        (V : Alfa_Violations.Vkind;
         E : Unique_Entity_Id) return Boolean
      is
        (Body_Violations (V).Contains (+E));

      function Get_Violation_Msg
        (V : Alfa_Violations.Vkind) return Unbounded_String
      is
        (Alfa_Violations.Violation_Msg (V));

      function Location return String is
        (Name_String (Chars (+Id)) & ' ' & Build_Location_String (Sloc (+Id)));
      --  Location string points to source location for entity. Use the
      --  location of the body (Defining_Entity) rather than the location
      --  of the spec (Id).

      ----------------------------
      -- Collect_Msg_Violations --
      ----------------------------

      function Collect_Msg_Violations
        (E : Unique_Entity_Id) return String
      is
         Msg : Unbounded_String;
      begin
         for V in Violation_Subkind loop
            if Has_Violation (V, E) then
               if Msg = "" then
                  Msg := Msg & Get_Violation_Msg (V);
               else
                  Msg := Msg & ", " & Get_Violation_Msg (V);
               end if;
            end if;
         end loop;

         if Msg /= "" then
            return Open & To_String (Msg) & Close;
         else
            return "";
         end if;
      end Collect_Msg_Violations;

      --------------------------------------
      -- Collect_Msg_Violations Instances --
      --------------------------------------

      function Collect_NYI_Msg_Violations is
        new Collect_Msg_Violations
          (Alfa_Violations.Not_Yet_Implemented, '[', ']');

      function Collect_NIR_Msg_Violations is
        new Collect_Msg_Violations (Alfa_Violations.Not_In_Roadmap, '(', ')');

      ------------
      -- Suffix --
      ------------

      function Suffix return String is
      begin
         if Body_Is_In_Alfa (Id) then
            return "";
         else
            declare
               NIR_Msg : constant String :=
                           Collect_NIR_Msg_Violations (Id);
               NYI_Msg : constant String :=
                           Collect_NYI_Msg_Violations (Id);
            begin
               if NIR_Msg /= "" and then NYI_Msg /= "" then
                  return ' ' & NIR_Msg & ' ' & NYI_Msg;
               elsif NIR_Msg /= "" then
                  return ' ' & NIR_Msg;
               elsif NYI_Msg /= "" then
                  return ' ' & NYI_Msg;
               else
                  raise Program_Error;
               end if;
            end;
         end if;
      end Suffix;

      C1, C2 : Character;
      --  Character indicates whether entity body (C1) and spec (C2) are:
      --    + in Alfa
      --    - not in Alfa roadmap
      --    * not yet implemented in Alfa

   begin
      if Comes_From_Source (+Id) then
         if Body_Is_In_Alfa (Id) then
            C1 := '+';
         elsif (for some V in Alfa_Violations.Not_In_Roadmap =>
                   Body_Violations (V).Contains (+Id)) then
            C1 := '-';
         else
            C1 := '*';
         end if;

         if Spec_Is_In_Alfa (Id) then
            C2 := '+';
         elsif (for some V in Alfa_Violations.Not_In_Roadmap =>
                   Spec_Violations (V).Contains (+Id)) then
            C2 := '-';
         else
            C2 := '*';
         end if;

         Put_Line (Output_File, C1 & C2 & ' ' & Location & Suffix);
      end if;
   end Generate_Output_In_Out_Alfa;

   -----------------------
   -- In_Main_Unit_Body --
   -----------------------

   function In_Main_Unit_Body (N : Node_Id) return Boolean is
      CU   : constant Node_Id := Enclosing_Lib_Unit_Node (N);
      Root : Node_Id;

   begin
      if No (CU) then
         return False;
      end if;

      Root := Unit (CU);

      case Nkind (Root) is
         when N_Package_Body    |
              N_Subprogram_Body =>

            return Is_Main_Cunit (Root);

         when N_Package_Declaration            |
              N_Generic_Package_Declaration    |
              N_Subprogram_Declaration         |
              N_Generic_Subprogram_Declaration =>

            return False;

         when N_Package_Renaming_Declaration           |
              N_Generic_Package_Renaming_Declaration   |
              N_Subprogram_Renaming_Declaration        |
              N_Generic_Function_Renaming_Declaration  |
              N_Generic_Procedure_Renaming_Declaration =>

            return False;

         when others =>
            raise Program_Error;
      end case;
   end In_Main_Unit_Body;

   -----------------------
   -- In_Main_Unit_Spec --
   -----------------------

   function In_Main_Unit_Spec (N : Node_Id) return Boolean is
      CU   : constant Node_Id := Enclosing_Lib_Unit_Node (N);
      Root : Node_Id;

   begin
      if No (CU) then
         return False;
      end if;

      Root := Unit (CU);

      case Nkind (Root) is
         when N_Package_Body    |
              N_Subprogram_Body =>

            return False;

         when N_Package_Declaration            |
              N_Generic_Package_Declaration    |
              N_Subprogram_Declaration         |
              N_Generic_Subprogram_Declaration =>

            return Is_Main_Cunit (Root)
              or else Is_Spec_Unit_Of_Main_Unit (Root);

         when N_Package_Renaming_Declaration           |
              N_Generic_Package_Renaming_Declaration   |
              N_Subprogram_Renaming_Declaration        |
              N_Generic_Function_Renaming_Declaration  |
              N_Generic_Procedure_Renaming_Declaration =>

            return False;

         when others =>
            raise Program_Error;
      end case;
   end In_Main_Unit_Spec;

   ------------------------
   -- Inherit_Violations --
   ------------------------

   procedure Inherit_Violations
     (A        : in out Violations;
      To, From : Unique_Entity_Id)
   is
   begin
      if Scope (+From) = Standard_Standard then
         A (NIR_XXX).Include (+To);
      else
         --  Either entity From was explicitly marked as not in Alfa, or it
         --  was not even visited because inside a generic, or task, etc.
         --  In the first case, inherit the reason for not being in Alfa.

         if (for some S of Spec_Violations => S.Contains (+From)) then
            for V in Alfa_Violations.Vkind loop
               if Spec_Violations (V).Contains (+From) then
                  A (V).Include (+To);
               end if;
            end loop;

         --  If From is from a generic instantiation, then mark the violation
         --  as being the current lack of support for generics.

         elsif Safe_Instantiation_Depth (From) > 0 then
            A (NYI_Generic).Include (+To);

         else
            A (NIR_XXX).Include (+To);
         end if;
      end if;
   end Inherit_Violations;

   ----------
   -- Mark --
   ----------

   procedure Mark (N : Node_Id) is
   begin
      --  Dispatch on node kind

      case Nkind (N) is
         when N_Defining_Identifier =>
            --  We represent types by their entity, instead of
            --  their declaration. Type identifiers be the only entities we
            --  come across.
            pragma Assert (Is_Type (N));
            Mark_Type_Entity (Unique (N));

         when N_Abstract_Subprogram_Declaration =>
            Mark_Non_Alfa ("abstract subprogram", N, NYI_Tagged);

         when N_Aggregate =>
            Mark_Non_Alfa ("aggregate", N, NYI_Aggregate);

         when N_Allocator =>
            Mark_Non_Alfa ("allocator", N, NIR_Dynamic_Alloc);

         when N_Assignment_Statement =>
            Mark (Name (N));
            Mark (Expression (N));

         when N_At_Clause =>
            Mark_Non_Alfa ("at clause", N, NYI_Rep_Clause);

         when N_Attribute_Reference =>
            Mark_Attribute_Reference (N);

         when N_Attribute_Definition_Clause   =>
            Mark_Non_Alfa ("attribute definition clause", N, NYI_Rep_Clause);

         when N_Binary_Op =>
            Mark_Binary_Op (N);

         when N_Block_Statement =>
            Mark_Non_Alfa ("block statement", N, NYI_Block_Statement);
            Mark_List (Declarations (N));
            Mark (Handled_Statement_Sequence (N));

         when N_Case_Expression | N_Case_Statement =>
            Mark (Expression (N));
            Mark_List (Alternatives (N));

         when N_Case_Expression_Alternative =>
            if Present (Actions (N)) then
               Mark_Non_Alfa
                 ("expression with action", N, NYI_Expr_With_Action);
            end if;
            Mark (Expression (N));

         when N_Case_Statement_Alternative =>
            Mark_List (Statements (N));

         when N_Code_Statement =>
            Mark_Non_Alfa ("code statement", N, NIR_Assembly_Lang);

         when N_Component_Declaration =>
            Mark_Component_Declaration (N);

         when N_Conditional_Expression =>
            Mark_Conditional_Expression (N);

         when N_Enumeration_Representation_Clause =>
            Mark_Non_Alfa
              ("enumeration representation clause", N, NYI_Rep_Clause);

         when N_Exception_Declaration          |
              N_Exception_Renaming_Declaration =>
            Mark_Non_Alfa_Declaration ("exception", N, NIR_Exception);

         when N_Exit_Statement =>
            if Present (Condition (N)) then
               Mark (Condition (N));
            end if;

         when N_Expanded_Name =>
            Mark_Identifier_Or_Expanded_Name (N);

         when N_Explicit_Dereference =>
            Mark_Non_Alfa ("explicit dereference", N, NIR_Access);

         when N_Expression_With_Actions =>
            declare
               Already_In_EWA : constant Boolean :=
                                  Inside_Expression_With_Actions;
            begin
               if not Already_In_EWA then
                  Inside_Expression_With_Actions := True;
               end if;

               Mark_List (Actions (N));
               Mark (Expression (N));

               if not Already_In_EWA then
                  Inside_Expression_With_Actions := False;
               end if;
            end;

         when N_Extended_Return_Statement =>
            Mark_Non_Alfa ("extended RETURN", N, NYI_XXX);

         when N_Extension_Aggregate =>
            Mark_Non_Alfa ("extension aggregate", N, NYI_Aggregate);

         when N_Formal_Object_Declaration |
              N_Formal_Package_Declaration |
              N_Formal_Subprogram_Declaration |
              N_Formal_Type_Declaration =>
            Mark_Non_Alfa_Declaration
              ("formal generic parameter", N, NYI_Generic);

         when N_Free_Statement =>
            Mark_Non_Alfa ("free statement", N, NIR_Dealloc);

         when N_Freeze_Entity =>
            null;

            --  Freeze may contain subprogram declarations that are not
            --  currently translated into Why, and are not known by code
            --  computing effects. Currently ignore them. See K523-005.

--              if Present (Actions (N)) then
--                 Mark_List (Actions (N));
--              end if;

         when N_Function_Call =>
            Mark_Call (N);

         when N_Function_Instantiation =>
            Mark_Non_Alfa ("function instantiation", N, NYI_Generic);

         when N_Generic_Function_Renaming_Declaration |
              N_Generic_Package_Declaration |
              N_Generic_Package_Renaming_Declaration |
              N_Generic_Procedure_Renaming_Declaration |
              N_Generic_Subprogram_Declaration =>
            Mark_Non_Alfa ("generic declaration", N, NYI_Generic);

         when N_Goto_Statement =>
            Mark_Non_Alfa ("goto statement", N, NIR_Goto);

         when N_Handled_Sequence_Of_Statements =>
            Mark_Handled_Statements (N);

         when N_Identifier =>
            Mark_Identifier_Or_Expanded_Name (N);

         when N_If_Statement =>
            Mark_If_Statement (N);

         --  Expansion rewrites complex membership tests into simpler ones

         when N_Membership_Test =>
            pragma Assert (No (Alternatives (N)));
            Mark (Left_Opnd (N));
            Mark (Right_Opnd (N));

         when N_Indexed_Component =>
            Mark (Prefix (N));
            Mark_List (Expressions (N));

         when N_Iterator_Specification =>
            Mark_Non_Alfa ("iterator specification", N, NYI_Container);

         when N_Loop_Statement =>
            if Present (Iteration_Scheme (N)) then
               Mark_Iteration_Scheme (Iteration_Scheme (N));
            end if;
            Mark_List (Statements (N));

         when N_Null =>
            Mark_Non_Alfa ("null", N, NIR_Access);

         when N_Object_Declaration =>
            Mark_Object_Declaration (N);

         when N_Object_Renaming_Declaration =>
            Mark_Object_Renaming_Declaration (N);

         when N_Unary_Op =>
            Mark_Unary_Op (N);

         when N_Package_Body =>
            Mark_Package_Body (N);

         when N_Package_Body_Stub =>
            Mark_Package_Body (Get_Body_From_Stub (N));

         when N_Package_Declaration =>
            Mark_Package_Declaration (N);

         when N_Package_Instantiation =>
            Mark_Non_Alfa ("package instantiation", N, NYI_Generic);

         when N_Package_Specification =>
            Mark_Package_Specification (N);

         when N_Parameter_Association =>
            Mark (Explicit_Actual_Parameter (N));

         when N_Pragma =>
            Mark_Pragma (N);

         when N_Procedure_Call_Statement =>
            Mark_Call (N);

         when N_Procedure_Instantiation =>
            Mark_Non_Alfa ("procedure instantiation", N, NYI_Generic);

         when N_Qualified_Expression =>
            Mark_Non_Alfa ("qualified expression", N, NYI_Qualification);

         when N_Quantified_Expression =>
            Mark (Condition (N));

         when N_Raise_Statement |
              N_Raise_xxx_Error =>
            Mark_Non_Alfa ("raise statement", N, NIR_Exception);

         when N_Range =>
            Mark (Low_Bound (N));
            Mark (High_Bound (N));

         when N_Record_Representation_Clause =>
            Mark_Non_Alfa ("record representation clause", N, NYI_Rep_Clause);

         when N_Reference =>
            Mark_Non_Alfa ("reference", N, NIR_Access);

         when N_Short_Circuit =>
            if Present (Actions (N)) then
               Mark_Non_Alfa
                 ("expression with action", N, NYI_Expr_With_Action);
            end if;
            Mark (Left_Opnd (N));
            Mark (Right_Opnd (N));

         when N_Simple_Return_Statement =>
            Mark_Simple_Return_Statement (N);

         when N_Selected_Component =>
            Mark (Prefix (N));
            Mark (Selector_Name (N));

         when N_Slice =>
            Mark_Non_Alfa ("slice", N, NYI_Slice);

         when N_Subprogram_Body =>
            if Acts_As_Spec (N) then
               Mark_Subprogram_Declaration (N);
            end if;
            Mark_Subprogram_Body (N);

         when N_Subprogram_Body_Stub =>
            if Is_Subprogram_Stub_Without_Prior_Declaration (N) then
               Mark_Subprogram_Declaration (Get_Body_From_Stub (N));
            end if;
            Mark_Subprogram_Body (Get_Body_From_Stub (N));

         when N_Subprogram_Declaration =>
            Mark_Subprogram_Declaration (N);

         when N_Type_Conversion =>
            Mark_Type_Conversion (N);

         when N_Unchecked_Expression =>
            Mark_Non_Alfa ("unchecked expression", N, NYI_XXX);

         when N_Unchecked_Type_Conversion =>
            if Comes_From_Source (N) then
               Mark_Non_Alfa
                 ("unchecked type conversion", N, NIR_Unchecked_Conv);
            else
               Mark (Expression (N));
            end if;

         when N_Validate_Unchecked_Conversion =>
            Mark_Non_Alfa ("unchecked conversion", N, NIR_Unchecked_Conv);

         when N_Variant_Part =>
            Mark_Non_Alfa ("variant part", N, NYI_Discriminant);

         when N_Full_Type_Declaration         |
              N_Subtype_Declaration           |
              N_Private_Extension_Declaration |
              N_Private_Type_Declaration      |
              N_Protected_Type_Declaration    |
              N_Task_Type_Declaration         =>
            Mark (Defining_Identifier (N));

         when N_String_Literal =>
            Mark_Non_Alfa ("string literal", N, NYI_String_Literal);

         when N_Abort_Statement            |
              N_Accept_Statement           |
              N_Asynchronous_Select        |
              N_Conditional_Entry_Call     |
              N_Delay_Relative_Statement   |
              N_Delay_Until_Statement      |
              N_Entry_Body                 |
              N_Entry_Call_Statement       |
              N_Entry_Declaration          |
              N_Protected_Body             |
              N_Protected_Body_Stub        |
              N_Requeue_Statement          |
              N_Selective_Accept           |
              N_Single_Task_Declaration    |
              N_Task_Body                  |
              N_Task_Body_Stub             |
              N_Timed_Entry_Call           =>
            Mark_Non_Alfa ("tasking", N, NIR_Tasking);

         --  The following kinds can be safely ignored by marking

         when N_Character_Literal               |
              N_Implicit_Label_Declaration      |
              N_Incomplete_Type_Declaration     |
              N_Integer_Literal                 |
              N_Itype_Reference                 |
              N_Label                           |
              N_Null_Statement                  |
              N_Number_Declaration              |
              N_Operator_Symbol                 |
              N_Others_Choice                   |
              N_Package_Renaming_Declaration    |
              N_Real_Literal                    |
              N_Subprogram_Info                 |
              N_Subprogram_Renaming_Declaration |
              N_Use_Package_Clause              |
              N_With_Clause                     |
              N_Use_Type_Clause                 =>
            null;

         --  The following kinds are rewritten by expansion

         when N_Expression_Function |
              N_Subunit             =>
            raise Program_Error;

         --  Mark should not be called on other kinds

         when N_Unused_At_Start |
              N_Component_Clause |
              N_Mod_Clause |
              N_Empty |
              N_Pragma_Argument_Association |
              N_Error |
              N_Defining_Character_Literal |
              N_Defining_Operator_Symbol |
              N_Subtype_Indication |
              N_Loop_Parameter_Specification |
              N_Function_Specification |
              N_Procedure_Specification |
              N_Access_Function_Definition | --  ???
              N_Access_Procedure_Definition | --  ???
              N_Constrained_Array_Definition  | --  ???
              N_Unconstrained_Array_Definition  | --  ???
              N_Accept_Alternative |
              N_Delay_Alternative |
              N_Elsif_Part |
              N_Entry_Body_Formal_Part |
              N_Iteration_Scheme |
              N_Terminate_Alternative |
              N_Push_Pop_xxx_Label |
              N_SCIL_Dispatch_Table_Tag_Init |
              N_SCIL_Dispatching_Call |
              N_SCIL_Membership_Test |
              N_Abortable_Part |
              N_Access_Definition |
              N_Access_To_Object_Definition |
              N_Aspect_Specification |
              N_Compilation_Unit |
              N_Compilation_Unit_Aux |
              N_Component_Association |
              N_Component_Definition |
              N_Component_List |
              N_Contract |
              N_Derived_Type_Definition |
              N_Decimal_Fixed_Point_Definition |
              N_Defining_Program_Unit_Name |
              N_Delta_Constraint |
              N_Designator |
              N_Digits_Constraint |
              N_Discriminant_Association |
              N_Discriminant_Specification |
              N_Enumeration_Type_Definition |
              N_Entry_Call_Alternative |
              N_Entry_Index_Specification |
              N_Exception_Handler |
              N_Floating_Point_Definition |
              N_Formal_Decimal_Fixed_Point_Definition |
              N_Formal_Derived_Type_Definition |
              N_Formal_Discrete_Type_Definition |
              N_Formal_Floating_Point_Definition |
              N_Formal_Modular_Type_Definition |
              N_Formal_Ordinary_Fixed_Point_Definition |
              N_Formal_Private_Type_Definition |
              N_Formal_Incomplete_Type_Definition |
              N_Formal_Signed_Integer_Type_Definition |
              N_Generic_Association |
              N_Index_Or_Discriminant_Constraint |
              N_Modular_Type_Definition |
              N_Ordinary_Fixed_Point_Definition |
              N_Parameter_Specification |
              N_Protected_Definition |
              N_Range_Constraint |
              N_Real_Range_Specification |
              N_Record_Definition |
              N_Signed_Integer_Type_Definition |
              N_Single_Protected_Declaration |
              N_Task_Definition |
              N_Triggering_Alternative |
              N_Variant |
              N_Unused_At_End =>
            raise Program_Error;
      end case;
   end Mark;

   ------------------------------
   -- Mark_Attribute_Reference --
   ------------------------------

   procedure Mark_Attribute_Reference (N : Node_Id) is
      Aname   : constant Name_Id      := Attribute_Name (N);
      P       : constant Node_Id      := Prefix (N);
      Exprs   : constant List_Id      := Expressions (N);
      Attr_Id : constant Attribute_Id := Get_Attribute_Id (Aname);

   begin
      case Attr_Id is
         when Attribute_Result =>
            null;

         when Attribute_Old =>
            if not Nkind_In (P, N_Identifier, N_Expanded_Name) then
               Mark_Non_Alfa ("'Old not applied to object name", N,
                              NYI_Old_Attribute);
            end if;

         when Attribute_First | Attribute_Last | Attribute_Length =>
            Mark (Prefix (N));

         when others =>
            Mark_Non_Alfa ("attribute", N, NYI_Attribute);
      end case;

      Mark (P);
      if Present (Exprs) then
         Mark_List (Exprs);
      end if;
   end Mark_Attribute_Reference;

   --------------------
   -- Mark_Binary_Op --
   --------------------

   procedure Mark_Binary_Op (N : Node_Id) is
      Left_T : constant Entity_Id := Etype (Left_Opnd (N));

   begin
      case N_Binary_Op'(Nkind (N)) is
         when N_Op_Concat =>
            Mark_Non_Alfa ("concatenation", N, NYI_Concatenation);

         when N_Op_Lt | N_Op_Le | N_Op_Gt | N_Op_Ge =>
            if Is_Boolean_Type (Left_T) then
               Mark_Non_Alfa
                 ("ordering operator on boolean type", N, NYI_Arith_Operation);

            elsif Is_Array_Type (Left_T) then
               Mark_Non_Alfa
                 ("ordering operator on array type", N, NYI_XXX);
            end if;

         when N_Op_Eq | N_Op_Ne =>
            if Is_Array_Type (Left_T) then
               Mark_Non_Alfa
                 ("equality operator on array type", N, NYI_XXX);
            end if;

         when N_Op_And | N_Op_Or =>
            if Is_Array_Type (Left_T)
              and then Nkind (N) in N_Binary_Op
            then
               Mark_Non_Alfa
                 ("binary operator on array type", N, NYI_XXX);
            end if;

         --  Do not allow arithmetic operations which could be reordered by the
         --  compiler, like "A + B - C", as a given ordering may overflow and
         --  another may not.

         when N_Op_Add | N_Op_Subtract =>
            if Nkind_In (Left_Opnd (N), N_Op_Add, N_Op_Subtract)
              and then Paren_Count (Left_Opnd (N)) = 0
            then
               Mark_Non_Alfa
                 ("possible re-ordering due to missing parentheses",
                  Left_Opnd (N), NIR_Ambiguous_Expr);
            end if;

            if Nkind_In (Right_Opnd (N), N_Op_Add, N_Op_Subtract)
              and then Paren_Count (Right_Opnd (N)) = 0
            then
               Mark_Non_Alfa
                 ("possible re-ordering due to missing parentheses",
                  Right_Opnd (N), NIR_Ambiguous_Expr);
            end if;

         when N_Op_Multiply | N_Op_Divide | N_Op_Rem | N_Op_Mod =>
            if Nkind (Left_Opnd (N)) in N_Multiplying_Operator
              and then Paren_Count (Left_Opnd (N)) = 0
            then
               Mark_Non_Alfa
                 ("possible re-ordering due to missing parentheses",
                  Left_Opnd (N), NIR_Ambiguous_Expr);
            end if;

            if Nkind (Right_Opnd (N)) in N_Multiplying_Operator
              and then Paren_Count (Right_Opnd (N)) = 0
            then
               Mark_Non_Alfa
                 ("possible re-ordering due to missing parentheses",
                  Right_Opnd (N), NIR_Ambiguous_Expr);
            end if;

         when N_Op_Expon |
              N_Op_Xor   |
              N_Op_Shift =>
            Mark_Non_Alfa ("operator", N, NYI_Arith_Operation);
      end case;

      Mark (Left_Opnd (N));
      Mark (Right_Opnd (N));
   end Mark_Binary_Op;

   ---------------
   -- Mark_Call --
   ---------------

   procedure Mark_Call (N : Node_Id) is
      Nam     : constant Node_Id := Name (N);
      Actuals : constant List_Id := Parameter_Associations (N);

   begin
      if Present (Actuals) then
         Mark_List (Actuals);
      end if;

      --  If this is an indirect call, an entry call, a call to a protected
      --  operation or the subprogram called is not in Alfa, then the call is
      --  not in Alfa.

      if not Is_Entity_Name (Nam) then
         Mark_Non_Alfa ("call", N, NIR_Indirect_Call);

      elsif not Spec_Is_In_Alfa (Unique (Entity (Nam))) then
         Mark_Non_Alfa ("subprogram called", N, From => Unique (Entity (Nam)));

      elsif In_Logic_Scope then

         if Has_Global_Reads (Entity (Nam)) then
            Mark_Non_Alfa ("global read in subprogram called in logic", N,
                           NYI_Logic_Function);

         elsif Nkind (Original_Node (Parent (Parent (Entity (Nam)))))
           /= N_Expression_Function
         then
            Mark_Non_Alfa ("regular function called in logic", N,
                           NYI_Logic_Function);
         end if;

      end if;
   end Mark_Call;

   ---------------------------
   -- Mark_Compilation_Unit --
   ---------------------------

   procedure Mark_Compilation_Unit (N : Node_Id) is
      CU        : constant Node_Id := Parent (N);
      Context_N : Node_Id;

   begin
      --  Separately mark declarations from Standard as in Alfa or not

      if Defining_Entity (N) = Standard_Standard then
         return;
      end if;

      Push_Scope (Unique_Entity_Id (Standard_Standard));

      Current_Unit_Is_Main_Body := In_Main_Unit_Body (N);
      Current_Unit_Is_Main_Spec := In_Main_Unit_Spec (N);

      Context_N := First (Context_Items (CU));
      while Present (Context_N) loop
         Mark (Context_N);
         Next (Context_N);
      end loop;

      Mark (N);
      Pop_Scope (Unique_Entity_Id (Standard_Standard));
   end Mark_Compilation_Unit;

   --------------------------------
   -- Mark_Component_Declaration --
   --------------------------------

   procedure Mark_Component_Declaration (N : Node_Id) is
      Def : constant Node_Id   := Component_Definition (N);

   begin
      if Aliased_Present (Def) then
         Mark_Non_Alfa_Declaration ("ALIASED", N, NIR_Access);
      end if;

      if Present (Access_Definition (Def)) then
         Mark_Non_Alfa ("access type", Def, NIR_Access);
      else
         Mark_Subtype_Indication (Subtype_Indication (Def));
      end if;
   end Mark_Component_Declaration;

   ---------------------------------
   -- Mark_Conditional_Expression --
   ---------------------------------

   procedure Mark_Conditional_Expression (N : Node_Id) is
      Condition : constant Node_Id := First (Expressions (N));
      Then_Expr : constant Node_Id := Next (Condition);
      Else_Expr : Node_Id;

   begin
      if Present (Then_Actions (N))
        or else Present (Else_Actions (N))
      then
         Mark_Non_Alfa ("expression with action", N, NYI_Expr_With_Action);
      end if;

      Else_Expr := Next (Then_Expr);

      Mark (Condition);
      Mark (Then_Expr);

      if Present (Else_Expr) then
         Mark (Else_Expr);
      end if;
   end Mark_Conditional_Expression;

   ---------------------------------
   -- Mark_Function_Specification --
   ---------------------------------

   procedure Mark_Function_Specification (N : Node_Id) is
      Id       : constant Entity_Id := Unique_Defining_Entity (N);
      Params   : constant List_Id   := Parameter_Specifications (N);
      Param    : Node_Id;
      Param_Id : Entity_Id;

   begin
      if Has_Global_Writes (Id) then
         Mark_Non_Alfa ("function with side-effect", Id, NYI_Impure_Function);
         return;
      end if;

      if Is_Non_Empty_List (Params) then
         Param := First (Params);
         while Present (Param) loop
            Param_Id := Defining_Identifier (Param);

            case Ekind (Param_Id) is
               when E_Out_Parameter =>
                  Mark_Non_Alfa ("function with OUT parameter", Id,
                                 NYI_Impure_Function);
                  return;
               when E_In_Out_Parameter =>
                  Mark_Non_Alfa ("function with IN OUT parameter", Id,
                                 NYI_Impure_Function);
                  return;
               when others =>
                  null;
            end case;

            Next (Param);
         end loop;
      end if;
   end Mark_Function_Specification;

   -----------------------------
   -- Mark_Handled_Statements --
   -----------------------------

   procedure Mark_Handled_Statements (N : Node_Id) is
      Handlers : constant List_Id := Exception_Handlers (N);

   begin
      if Present (Handlers) then
         Mark_Non_Alfa ("handler", First (Handlers), NIR_Exception);
      end if;

      Mark_List (Statements (N));
   end Mark_Handled_Statements;

   ---------------------
   -- Mark_Identifier --
   ---------------------

   procedure Mark_Identifier_Or_Expanded_Name (N : Node_Id) is
      E : Unique_Entity_Id;
   begin
      if Is_Entity_Name (N) then
         E := Unique (Entity (N));

         case Ekind (+E) is
            when Object_Kind =>
               if Ekind_In (+E, E_Variable, E_Constant)
                 and then not (Object_Is_In_Alfa (E))
               then
                  Mark_Non_Alfa ("object", N, From => Unique (Entity (N)));
               end if;

            when Type_Kind =>
               if not Type_Is_In_Alfa (Entity (N)) then
                  Mark_Non_Alfa ("type", N, From => Unique (Entity (N)));
               end if;

            --  Subprogram name appears for example in Sub'Result

            when E_Enumeration_Literal |
                 Subprogram_Kind       =>
               null;

            when others =>
               Mark_Non_Alfa ("entity", N, From => Unique (Entity (N)));
         end case;
      end if;
   end Mark_Identifier_Or_Expanded_Name;

   ----------------------
   -- Mark_Type_Entity --
   ----------------------

   procedure Mark_Type_Entity (Id : Unique_Entity_Id)
   is
   begin
      Push_Scope (Id);
      Mark_Type_Definition (Id);
      Pop_Scope (Id);

      --  If type is in Alfa, store this information explicitly

      Mark_Type_In_Alfa (Id, In_Alfa => Type_Is_Computed_In_Alfa (Id));
      Mark_Type_Declaration (Id);
   end Mark_Type_Entity;

   -----------------------
   -- Mark_If_Statement --
   -----------------------

   procedure Mark_If_Statement (N : Node_Id) is
   begin
      Mark (Condition (N));

      Mark_List (Then_Statements (N));

      if Present (Elsif_Parts (N)) then
         declare
            Part : Node_Id;

         begin
            Part := First (Elsif_Parts (N));
            while Present (Part) loop
               Mark (Condition (Part));
               Mark_List (Then_Statements (Part));

               if Present (Condition_Actions (Part)) then
                  Mark_Non_Alfa
                    ("expression with action", N, NYI_Expr_With_Action);
               end if;

               Next (Part);
            end loop;
         end;
      end if;

      if Present (Else_Statements (N)) then
         Mark_List (Else_Statements (N));
      end if;
   end Mark_If_Statement;

   ---------------------------
   -- Mark_Iteration_Scheme --
   ---------------------------

   procedure Mark_Iteration_Scheme (N : Node_Id) is
   begin
      if Present (Condition_Actions (N)) then
         Mark_Non_Alfa ("expression with action", N, NYI_Expr_With_Action);
      end if;

      if Present (Condition (N)) then
         Mark (Condition (N));

      elsif Present (Loop_Parameter_Specification (N)) then
         --  The entity for iterating over a loop is always in Alfa
         null;

      else
         pragma Assert (Present (Iterator_Specification (N)));
         Mark_Non_Alfa ("loop with iterator", N, NYI_XXX);
      end if;
   end Mark_Iteration_Scheme;

   ---------------
   -- Mark_List --
   ---------------

   procedure Mark_List (L : List_Id) is
      N : Node_Id;
   begin
      N := First (L);
      while Present (N) loop
         Mark (N);
         Next (N);
      end loop;
   end Mark_List;

   -------------------
   -- Mark_Non_Alfa --
   -------------------

   procedure Mark_Non_Alfa
     (Msg    : String;
      N      : Node_Id;
      V      : Alfa_Violations.Vkind;
      Silent : Boolean        := False)
   is
      procedure Mark_Body_Violations (E : Unique_Entity_Id);
      procedure Mark_Spec_Violations (E : Unique_Entity_Id);

      procedure Mark_Body_Violations (E : Unique_Entity_Id) is
      begin
         Body_Violations (V).Include (+E);
      end Mark_Body_Violations;

      procedure Mark_Spec_Violations (E : Unique_Entity_Id) is
      begin
         Spec_Violations (V).Include (+E);
      end Mark_Spec_Violations;

      procedure Mark_All_Scopes is new Mark_Violations_For_All_Scopes;

   begin
      --  If formal proof is forced and node N is not compiler-generated, then
      --  notify the user about the violation.

      if Force_Alfa (N)
        and then not Silent
        and then Comes_From_Source (N)
      then
         Error_Msg_F (Complete_Error_Msg (Msg, V), N);
      end if;

      Mark_All_Scopes;
   end Mark_Non_Alfa;

   procedure Mark_Non_Alfa
     (Msg  : String;
      N    : Node_Id;
      From : Unique_Entity_Id)
   is
      procedure Mark_Body_Violations (E : Unique_Entity_Id);
      procedure Mark_Spec_Violations (E : Unique_Entity_Id);

      procedure Mark_Body_Violations (E : Unique_Entity_Id) is
      begin
         Inherit_Violations (Body_Violations, From => From, To => E);
      end Mark_Body_Violations;

      procedure Mark_Spec_Violations (E : Unique_Entity_Id) is
      begin
         Inherit_Violations (Spec_Violations, From => From, To => E);
      end Mark_Spec_Violations;

      procedure Mark_All_Scopes is new Mark_Violations_For_All_Scopes;

   begin
      --  If formal proof is forced and node N is not compiler-generated, then
      --  notify the user about the violation.

      if Force_Alfa (N)
        and then Comes_From_Source (N)
      then
         if Scope (+From) = Standard_Standard
           or else Spec_Violations (NIR_XXX).Contains (+From)
         then
            Error_Msg_F (Complete_Error_Msg (Msg, NIR_XXX), N);

         elsif (for some V in Alfa_Violations.Not_In_Roadmap =>
                  Spec_Violations (V).Contains (+From))
         then
            for V in Alfa_Violations.Not_In_Roadmap loop
               if Spec_Violations (V).Contains (+From) then
                  Error_Msg_F (Complete_Error_Msg (Msg, V), N);
               end if;
            end loop;

         elsif (for some V in Alfa_Violations.Not_Yet_Implemented =>
                  Spec_Violations (V).Contains (+From))
         then
            for V in Alfa_Violations.Not_Yet_Implemented loop
               if Spec_Violations (V).Contains (+From) then
                  Error_Msg_F (Complete_Error_Msg (Msg, V), N);
               end if;
            end loop;

         --  If From is from a generic instantiation, then mark the violation
         --  as being the current lack of support for generics.

         elsif Safe_Instantiation_Depth (From) > 0 then
            Error_Msg_F (Complete_Error_Msg (Msg, NYI_Generic), N);

         else
            Error_Msg_F (Complete_Error_Msg (Msg, NIR_XXX), N);
         end if;
      end if;

      Mark_All_Scopes;
   end Mark_Non_Alfa;

   -------------------------------
   -- Mark_Non_Alfa_Declaration --
   -------------------------------

   procedure Mark_Non_Alfa_Declaration
     (Msg    : String;
      N      : Node_Id;
      V      : Alfa_Violations.Vkind;
      Silent : Boolean        := False) is
   begin
      Spec_Violations (V).Include (Unique_Defining_Entity (N));
      Mark_Non_Alfa (Msg, N, V, Silent);
   end Mark_Non_Alfa_Declaration;

   procedure Mark_Non_Alfa_Declaration
     (Msg  : String;
      N    : Node_Id;
      From : Unique_Entity_Id) is
   begin
      Inherit_Violations
        (Spec_Violations, From => From, To => Unique (Defining_Entity (N)));
      Mark_Non_Alfa (Msg, N, From);
   end Mark_Non_Alfa_Declaration;

   -----------------------------
   -- Mark_Object_Declaration --
   -----------------------------

   procedure Mark_Object_Declaration (N : Node_Id) is
      Id   : constant Unique_Entity_Id := Unique (Defining_Entity (N));
      Def  : constant Node_Id          := Object_Definition (N);
      Expr : constant Node_Id          := Expression (N);
      T    : constant Entity_Id        := Etype (+Id);

   begin
      --  Ignore exact value of deferred constants, so that these can be
      --  used for a parametrized proof. This is detected here by noting that
      --  the object is already explicitly in or out of Alfa. Not adding the
      --  declaration to the set of Alfa declarations is also crucial to avoid
      --  a redundant declaration in Why.

      if Object_Is_In_Alfa (Id)
        or else not Object_Is_Computed_In_Alfa (Id)
      then
         Mark (Expr);
         return;
      end if;

      --  The object is in Alfa if-and-only-if its type is in Alfa and it is
      --  not aliased.

      Push_Scope (Id);
      if not Type_Is_In_Alfa (T) then
         Mark_Non_Alfa ("type", Def, From => Unique (T));
      end if;

      if Aliased_Present (N) then
         Mark_Non_Alfa ("ALIASED", N, NIR_Access);
      end if;

      if Present (Expr) then
         Mark (Expr);
      end if;

      Pop_Scope (Id);

      --  If object is in Alfa, store this information explicitly

      Mark_Object_In_Alfa (Id, N, In_Alfa => Object_Is_Computed_In_Alfa (Id));
   end Mark_Object_Declaration;

   --------------------------------------
   -- Mark_Object_Renaming_Declaration --
   --------------------------------------

   procedure Mark_Object_Renaming_Declaration (N : Node_Id) is
   begin
      Mark_Non_Alfa_Declaration ("object being renamed", N, NYI_XXX);
   end Mark_Object_Renaming_Declaration;

   -----------------------
   -- Mark_Package_Body --
   -----------------------

   procedure Mark_Package_Body (N : Node_Id) is
      Id  : constant Unique_Entity_Id := Unique (Defining_Entity (N));

   begin
      --  Currently do not analyze generic bodies

      if Ekind (Unique_Defining_Entity (N)) = E_Generic_Package then
         Mark_Non_Alfa_Declaration ("generic", N, NYI_Generic);
         return;
      end if;

      --  The scope entity for a package body is not the same as the scope
      --  entity for a package declaration, which allow separately forcing
      --  formal proof on either the declaration or the body.

      Push_Scope (Id);
      Mark_List (Declarations (N));
      Pop_Scope (Id);
   end Mark_Package_Body;

   ------------------------------
   -- Mark_Package_Declaration --
   ------------------------------

   procedure Mark_Package_Declaration (N : Node_Id) is
      Id : constant Unique_Entity_Id := Unique (Defining_Entity (N));

   begin
      --  Rewriting of a package should only occur for a package instantiation,
      --  in which case Is_Rewrite_Insertion return True. Currently do not
      --  analyze generic package instantiations.

      if Is_Rewrite_Insertion (N)
        or else Nkind (Original_Node (N)) = N_Package_Instantiation
      then
         Mark_Non_Alfa_Declaration ("generic", N, NYI_Generic);
         return;
      end if;

      Push_Scope (Id);
      Mark (Specification (N));
      Pop_Scope (Id);
   end Mark_Package_Declaration;

   --------------------------------
   -- Mark_Package_Specification --
   --------------------------------

   procedure Mark_Package_Specification (N : Node_Id) is
      Vis_Decls  : constant List_Id := Visible_Declarations (N);
      PriNYI_Decls : constant List_Id := Private_Declarations (N);

   begin
      if Present (Vis_Decls) then
         Mark_List (Vis_Decls);
      end if;

      if Present (PriNYI_Decls) then
         Mark_List (PriNYI_Decls);
      end if;
   end Mark_Package_Specification;

   -----------------
   -- Mark_Pragma --
   -----------------

   procedure Mark_Pragma (N : Node_Id) is
      Pname   : constant Name_Id   := Pragma_Name (N);
      Prag_Id : constant Pragma_Id := Get_Pragma_Id (Pname);

      Arg  : Node_Id;
      Arg1 : Node_Id;
      Arg2 : Node_Id;
      --  First two pragma arguments (pragma argument association nodes, or
      --  Empty if the corresponding argument does not exist).

   begin
      if Present (Pragma_Argument_Associations (N)) then
         Arg1 := First (Pragma_Argument_Associations (N));

         if Present (Arg1) then
            Arg2 := Next (Arg1);
         end if;
      end if;

      Error_Msg_Name_1 := Pname;

      case Prag_Id is

         --  pragma Annotate (IDENTIFIER [, IDENTIFIER {, ARG}]);
         --  ARG ::= NAME | EXPRESSION

         --  The first two arguments are by convention intended to refer to an
         --  external tool and a tool-specific function. These arguments are
         --  not analyzed.

         --  The following is a special form used in conjunction with the
         --  Alfa subset of Ada:

         --    pragma Annotate (GNATprove, MODE);
         --    MODE ::= Force | Ignore

         --    This pragma either forces (mode Force) or disables (mode Ignore)
         --    formal verification of the subprogram in which it is added. When
         --    formal verification is forced, all violations of the the Alfa
         --    subset of Ada present in the subprogram are reported as errors
         --    to the user.

         when Pragma_Annotate =>

            --  Fill in Name_Buffer with Name_GNATprove so that Name_Find
            --  returns the corresponding name.

            Name_Len := 0;
            Add_Str_To_Name_Buffer (Name_GNATprove);

            if Chars (Get_Pragma_Arg (Arg1)) = Name_Find then
               if List_Length (Pragma_Argument_Associations (N)) /= 2 then
                  Error_Msg_N ("wrong number of arguments for annotation", N);
                  return;
               end if;

               Arg := Get_Pragma_Arg (Arg2);
               if Nkind (Arg) /= N_Identifier then
                  Error_Msg_N
                    ("argument for pragma must be an identifier", Arg2);
                  return;
               end if;

               declare
                  Cur_Ent : constant Unique_Entity_Id := Current_Scope.Entity;

               begin
                  pragma Assert (Is_Subprogram (+Cur_Ent)
                                  or else Ekind (+Cur_Ent) = E_Package
                                  or else Ekind (+Cur_Ent) = E_Package_Body);

                  --  Check that this is the first occurrence of this pragma
                  --  on the current entity.

                  if Formal_Proof_On.Contains (+Cur_Ent) then
                     Error_Msg_N ("formal proof already forced for entity", N);
                     return;

                  elsif Formal_Proof_Off.Contains (+Cur_Ent) then
                     Error_Msg_N
                       ("formal proof already disabled for entity", N);
                     return;
                  end if;

                  if Chars (Arg) = Name_Force then
                     if Formal_Proof_Currently_Forced then
                        Error_Msg_N ("?formal proof already forced", N);
                     end if;
                     Formal_Proof_On.Insert (+Cur_Ent);
                  elsif Chars (Arg) = Name_Ignore then
                     if Formal_Proof_Currently_Disabled then
                        Error_Msg_N ("?formal proof already disabled", N);
                     end if;
                     Formal_Proof_Off.Insert (+Cur_Ent);
                  else
                     Error_Msg_N ("second argument for annotation must be "
                                  & "Force or Ignore", Arg2);
                        return;
                  end if;

                  --  Notify user if some Alfa violation occurred before this
                  --  point in Cur_Ent. These violations are not precisly
                  --  located, but this is better than ignoring these
                  --  violations.

                  if Chars (Arg) = Name_Force
                    and then (not Spec_Is_Computed_In_Alfa (Cur_Ent)
                               or else not Body_Is_Computed_In_Alfa (Cur_Ent))
                  then
                     Error_Msg_N
                       ("annotation is placed after violation of Alfa", N);
                     return;
                  end if;
               end;
            end if;

         --  Pragma Pre/Postconditions are ignored

         when Pragma_Precondition | Pragma_Postcondition =>
            null;

         --  pragma Check ([Name    =>] Identifier,
         --                [Check   =>] Boolean_Expression
         --              [,[Message =>] String_Expression]);

         when Pragma_Check =>

            --  Pragma Check generated for Pre/Postconditions are ignored

            if Chars (Get_Pragma_Arg (Arg1)) /= Name_Precondition
              and then Chars (Get_Pragma_Arg (Arg1)) /= Name_Postcondition
            then
               Push_Logic_Scope;
               Mark (Get_Pragma_Arg (Arg2));
               Pop_Logic_Scope;
            end if;

         when others =>
            Mark_Non_Alfa ("pragma", N, NYI_Pragma);
      end case;
   end Mark_Pragma;

   ----------------------------------
   -- Mark_Simple_Return_Statement --
   ----------------------------------

   procedure Mark_Simple_Return_Statement (N : Node_Id) is
   begin
      if Present (Expression (N)) then
         Mark (Expression (N));
      end if;
   end Mark_Simple_Return_Statement;

   ---------------------------
   -- Mark_Standard_Package --
   ---------------------------

   procedure Mark_Standard_Package is
   begin
      for S in S_Types loop
         if Standard_Type_Is_In_Alfa (S) then
            Standard_In_Alfa.Insert (Standard_Entity (S));
            Standard_In_Alfa.Include (Etype (Standard_Entity (S)));
         end if;
      end loop;

      Standard_In_Alfa.Insert (Standard_False);
      Standard_In_Alfa.Insert (Standard_True);

      Standard_In_Alfa.Insert (Universal_Integer);

      Standard_In_Alfa.Insert (Standard_Integer_8);
      Standard_In_Alfa.Insert (Standard_Integer_16);
      Standard_In_Alfa.Insert (Standard_Integer_32);
      Standard_In_Alfa.Insert (Standard_Integer_64);
   end Mark_Standard_Package;

   --------------------------
   -- Mark_Subprogram_Body --
   --------------------------

   procedure Mark_Subprogram_Body (N : Node_Id) is
      Id  : constant Unique_Entity_Id := Unique (Defining_Entity (N));
      HSS : constant Node_Id          := Handled_Statement_Sequence (N);

   begin

      if not (Current_Unit_Is_Main_Spec or Current_Unit_Is_Main_Body) then
         return;
      end if;

      --  Currently do not analyze generic bodies

      if Ekind (+Id) in Generic_Subprogram_Kind then
         Mark_Non_Alfa_Declaration ("generic", N, NYI_Generic);
         return;
      end if;

      --  Even if the subprogram we consider is not in Alfa, we still need to
      --  generate object declarations for its parameters; This is necessary
      --  to support local subprograms which use these parameters, which may
      --  be in Alfa.

      declare
         Param : Entity_Id := First_Entity (+Id);
      begin
         while Present (Param) loop
            if Nkind (Parent (Param)) = N_Parameter_Specification then
               if Type_Is_In_Alfa (Etype (Param)) then
                  Decls_In_Body (Alfa_Object).Append (Parent (Param));
               else
                  Decls_In_Body (Non_Alfa_Type).Append (Parent (Param));
               end if;
            end if;
            Next_Entity (Param);
         end loop;
      end;

      --  Inherit violations from spec to body

      if not Spec_Is_In_Alfa (Id) then
         Inherit_Violations (Body_Violations, From => Id, To => Id);
      end if;

      --  Detect violations in the body itself

      Push_Scope (Id, Is_Body => True);
      Mark_List (Declarations (N));
      Mark (HSS);
      Pop_Scope (Id);

      --  If body is in Alfa, store this information explicitly

      if Body_Is_Computed_In_Alfa (Id) then
         Mark_Body_In_Alfa (Id, N);
      end if;

      --  Postprocessing: indicate in output file if subprogram is in Alfa or
      --  not, for debug and verifications.

      Generate_Output_In_Out_Alfa (Id);
   end Mark_Subprogram_Body;

   ---------------------------------
   -- Mark_Subprogram_Declaration --
   ---------------------------------

   --  N is either a subprogram declaration node, or a subprogram body node
   --  for those subprograms which do not have a prior declaration (not
   --  counting a stub as a declaration).

   procedure Mark_Subprogram_Declaration (N : Node_Id) is
      PPC  : Node_Id;
      Expr : Node_Id;
      Id   : constant Unique_Entity_Id := Unique (Defining_Entity (N));

   begin
      --  Currently do not analyze generic instantiations

      if Nkind (Original_Node (N)) in N_Subprogram_Instantiation
        or else Ekind (+Id) in Generic_Subprogram_Kind
      then
         Mark_Non_Alfa_Declaration ("generic", N, NYI_Generic);
         return;
      end if;

      Push_Scope (Id);
      Mark_Subprogram_Specification (Specification (N));

      Push_Logic_Scope;
      PPC := Spec_PPC_List (Contract (+Id));
      while Present (PPC) loop
         Expr := Get_Pragma_Arg (First (Pragma_Argument_Associations (PPC)));
         Mark (Expr);
         PPC := Next_Pragma (PPC);
      end loop;
      Pop_Logic_Scope;

      Pop_Scope (Id);

      --  If spec is in Alfa, store this information explicitly

      if Spec_Is_Computed_In_Alfa (Id) then
         Mark_Spec_In_Alfa (Id, N);
      end if;
   end Mark_Subprogram_Declaration;

   -----------------------------------
   -- Mark_Subprogram_Specification --
   -----------------------------------

   procedure Mark_Subprogram_Specification (N : Node_Id) is
      Id         : constant Entity_Id := Unique_Defining_Entity (N);
      Formals    : constant List_Id   := Parameter_Specifications (N);
      Param_Spec : Node_Id;
      Formal     : Entity_Id;

   begin

      if Ekind (Id) = E_Function then
         Mark_Function_Specification (N);
      end if;

      if Present (Formals) then
         Param_Spec := First (Formals);
         while Present (Param_Spec) loop
            Formal := Defining_Identifier (Param_Spec);

            --  The parameter is in Alfa if-and-only-if its type is in Alfa

            if not Type_Is_In_Alfa (Etype (Formal)) then
               Mark_Non_Alfa_Declaration
                 ("type of formal", Param_Spec,
                  From => Unique (Etype (Formal)));
            end if;

            Next (Param_Spec);
         end loop;
      end if;

      --  If the result type of a subprogram is not in Alfa, then the
      --  subprogram is not in Alfa.

      if Nkind (N) = N_Function_Specification
        and then not Type_Is_In_Alfa (Etype (Id))
      then
         Mark_Non_Alfa
           ("return type", Result_Definition (N),
            From => Unique (Etype (Id)));
      end if;
   end Mark_Subprogram_Specification;

   -----------------------------
   -- Mark_Subtype_Indication --
   -----------------------------

   procedure Mark_Subtype_Indication (N : Node_Id) is
      T       : Entity_Id;
      Cstr    : Node_Id;

   begin
      if Nkind (N) = N_Subtype_Indication then
         T := Etype (Subtype_Mark (N));
      else
         T := Etype (N);
      end if;

      --  Check that the base type is in Alfa

      if not Type_Is_In_Alfa (T) then
         Mark_Non_Alfa ("base type", N, From => Unique (T));
      elsif Is_Array_Type (T) then
         Mark_Non_Alfa ("array subtype", N, NYI_Array_Subtype);
      end if;

      if Nkind (N) = N_Subtype_Indication then

         Cstr := Constraint (N);
         case Nkind (Cstr) is
            when N_Range_Constraint =>
               if not Is_Static_Range (Range_Expression (Cstr)) then
                  Mark_Non_Alfa ("non-static range", N, NYI_Non_Static_Range);
               end if;

            when N_Index_Or_Discriminant_Constraint =>

               if Is_Array_Type (+T) then
                  Cstr := First (Constraints (Cstr));
                  while Present (Cstr) loop

                     case Nkind (Cstr) is
                     when N_Identifier | N_Expanded_Name =>
                        if not Type_Is_In_Alfa (Entity (Cstr)) then
                           Mark_Non_Alfa
                             ("index type", N, From => Unique (Entity (Cstr)));
                        end if;

                     when N_Subtype_Indication =>  --  TO DO
                        Mark_Non_Alfa
                          ("index type", N, NYI_XXX);

                     when N_Range =>
                        if Comes_From_Source (N) and then
                          not Is_Static_Range (Cstr) then
                           Mark_Non_Alfa
                             ("non-static range", N, NYI_Non_Static_Range);
                        end if;

                     when others =>
                        raise Program_Error;
                     end case;
                     Next (Cstr);
                  end loop;

               --  Note that a discriminant association that has no selector
               --  name list appears directly as an expression in the tree.

               else
                  Mark_Non_Alfa ("discriminant", N, NYI_Discriminant);
               end if;

            when N_Digits_Constraint =>
               Mark_Non_Alfa ("digits constraint", N, NYI_Float);

            when N_Delta_Constraint =>
               Mark_Non_Alfa ("delta constraint", N, NYI_Float);

            when others =>  --  TO DO ???
               raise Program_Error;
         end case;
      end if;
   end Mark_Subtype_Indication;

   --------------------------
   -- Mark_Type_Conversion --
   --------------------------

   procedure Mark_Type_Conversion (N : Node_Id) is
      Expr : constant Node_Id := Expression (N);

   begin
      --  Type conversion between scalar types are allowed in Alfa. All other
      --  type conversions are not allowed.

      if not (Is_Scalar_Type (Etype (Expr))
               and then Is_Scalar_Type (Etype (N)))
      then
         Mark_Non_Alfa
           ("type conversion not between scalar types", N, NYI_Conversion);
      end if;

      Mark (Expr);
   end Mark_Type_Conversion;

   --------------------------
   -- Mark_Type_Definition --
   --------------------------

   procedure Mark_Type_Definition (Id : Unique_Entity_Id) is
   begin
      if Is_Tagged_Type (+Id) then
         Mark_Non_Alfa ("tagged type", +Id, NYI_Tagged);
      end if;

      case Ekind (+Id) is
         when Array_Kind =>
            declare
               Component_Typ : constant Node_Id := Component_Type (+Id);
               Index         : Node_Id := First_Index (+Id);

            begin

               --  Check that all index types are in Alfa

               while Present (Index) loop
                  if not Type_Is_In_Alfa (Etype (Index)) then
                     Mark_Non_Alfa
                       ("index type", +Id, From => Unique (Etype (Index)));
                  end if;
                  Next_Index (Index);
               end loop;

               --  Access definition for component type is not in Alfa

               if No (Component_Typ) then
                  Mark_Non_Alfa ("access type", +Id, NIR_Access);
               end if;

               --  Check that component type is in Alfa

               if not Type_Is_In_Alfa (Component_Typ) then
                  Mark_Non_Alfa
                    ("component type", +Id,
                     From => Unique (Component_Typ));
               end if;

               --  Check that array bounds are static

               if Is_Constrained (+Id)
                 and then not Has_Static_Array_Bounds (+Id)
               then
                  Mark_Non_Alfa
                    ("array type with non-static bounds",
                     +Id, NYI_Non_Static_Range);
               end if;
            end;

         when Enumeration_Kind =>

            --  Enumeration type is in Alfa only if it is not a character type

            if not (Is_Static_Range (Scalar_Range (+Id))) then
               Mark_Non_Alfa
                 ("enumeration type with dynamic range", +Id,
                  NYI_Non_Static_Range);
            end if;
            if Is_Character_Type (+Id) then
               Mark_Non_Alfa ("character enumeration type", +Id, NYI_XXX);
            end if;

         when Signed_Integer_Kind =>
            if not (Is_Static_Range (Scalar_Range (+Id))) then
               Mark_Non_Alfa
                 ("integer type with dynamic range", +Id,
                  NYI_Non_Static_Range);
            end if;

         when E_Record_Type =>
            if Is_Interface (+Id) then
               Mark_Non_Alfa ("interface", +Id, NYI_XXX);

            else
               declare
                  Field : Node_Id := First_Entity (+Id);
                  Typ   : Entity_Id;

               begin
                  Push_Scope (Id);

                  while Present (Field) loop
                     Typ := Etype (Field);

                     if Ekind (Field) in Object_Kind
                       and then not Type_Is_In_Alfa (Typ)
                     then
                        Mark_Non_Alfa
                          ("component type", Typ, From => Unique (Typ));
                     end if;

                     Next_Entity (Field);
                  end loop;

                  Pop_Scope (Id);
               end;
            end if;

         when E_Class_Wide_Type    |
              E_Class_Wide_Subtype =>
            Mark_Non_Alfa ("type definition", +Id, NYI_XXX);

         when E_Record_Subtype =>
            Mark_Non_Alfa ("type definition", +Id, NYI_Discriminant);

         when E_Modular_Integer_Type | E_Modular_Integer_Subtype
            | Real_Kind  =>
            Mark_Non_Alfa ("type definition", +Id, NYI_Modular);

         when Access_Kind =>
            Mark_Non_Alfa ("access type", +Id, NIR_Access);

         when Concurrent_Kind =>
            Mark_Non_Alfa ("tasking", +Id, NIR_Tasking);

         when Private_Kind =>

            --  In simple cases, the unique entity of a private type is the
            --  entity with the completing declaration. If the completing
            --  declaration is a derived type or subtype of another private
            --  type, this is not the case, and only in such situations we
            --  should fall in this branch.
            --  See also gnat/einfo.ads, Full_View and Underlying_Full_View.
            --  The private type we consider is in Alfa if the underlying type
            --  is in Alfa.

            Mark (Underlying_Type (+Id));

         when others =>
            raise Program_Error;
      end case;
   end Mark_Type_Definition;

   -------------------
   -- Mark_Unary_Op --
   -------------------

   procedure Mark_Unary_Op (N : Node_Id) is
      T : constant Entity_Id := Etype (Right_Opnd (N));

   begin
      case N_Unary_Op'(Nkind (N)) is
         when N_Op_Not =>
            if Is_Array_Type (T) then
               Mark_Non_Alfa
                 ("not operator on array type", N, NYI_Arith_Operation);
            end if;

         when N_Op_Abs =>
            Mark_Non_Alfa ("abs operator", N, NYI_Arith_Operation);

         when N_Op_Plus | N_Op_Minus =>
            null;
      end case;

      Mark (Right_Opnd (N));
   end Mark_Unary_Op;

   ---------------------
   -- Mark_Violations --
   ---------------------

   procedure Mark_Violations (Scop : Scope_Record) is
      Ent : Unique_Entity_Id;

   begin
      if Scop.Is_Logic then
         return;
      end if;

      Ent := Scop.Entity;
      case Ekind (+Ent) is

         --  Detect violation in initialization of package-level object

         when Object_Kind =>
            if Scop.Is_Body then
               Mark_Body_Violations (Ent);
            else
               Mark_Spec_Violations (Ent);
            end if;

         when Type_Kind =>
            pragma Assert (not Scop.Is_Body);
            Mark_Spec_Violations (Ent);

         when E_Package | E_Package_Body | E_Generic_Package =>
            null;

         --  Detect violation in subprogram declarations and subprogram bodies

         --  If the non-Alfa construct is in a precondition or postcondition,
         --  then mark the subprogram as not in Alfa, because neither the
         --  subprogram nor its callers can be proved formally.
         --
         --  If the non-Alfa construct is in a regular piece of code inside
         --  the body of the subprogram, then mark the subprogram body as not
         --  in Alfa, because the subprogram cannot be proved formally, but its
         --  callers could.

         when Subprogram_Kind =>
            if Scop.Is_Body then
               Mark_Body_Violations (Ent);
            else
               Mark_Spec_Violations (Ent);
            end if;

         when others =>
            raise Program_Error;
      end case;
   end Mark_Violations;

   ------------------------------------
   -- Mark_Violations_For_All_Scopes --
   ------------------------------------

   procedure Mark_Violations_For_All_Scopes is
      procedure Mark_Scope is new Mark_Violations;
   begin
      for S in First_Scope_Index .. Scope_Stack.Last loop
         Mark_Scope (Scope_Stack.Table (S));
      end loop;
   end Mark_Violations_For_All_Scopes;

   ---------------------
   -- Pop_Logic_Scope --
   ---------------------

   procedure Pop_Logic_Scope is
      Cur_Scop : Scope_Record renames Scope_Stack.Table (Scope_Stack.Last);
   begin
      pragma Assert (Cur_Scop.Is_Logic);
      Scope_Stack.Decrement_Last;
   end Pop_Logic_Scope;

   ---------------
   -- Pop_Scope --
   ---------------

   procedure Pop_Scope (E : Unique_Entity_Id) is
      Cur_Scop : Scope_Record renames Scope_Stack.Table (Scope_Stack.Last);
   begin
      pragma Assert (Cur_Scop.Entity = E);
      Scope_Stack.Decrement_Last;
   end Pop_Scope;

   ----------------------
   -- Push_Logic_Scope --
   ----------------------

   procedure Push_Logic_Scope is
   begin
      Scope_Stack.Increment_Last;
      Scope_Stack.Table (Scope_Stack.Last) := Scope_Record'(Is_Logic => True);
   end Push_Logic_Scope;

   ----------------
   -- Push_Scope --
   ----------------

   procedure Push_Scope
     (E          : Unique_Entity_Id;
      Is_Body    : Boolean := False) is
   begin
      Scope_Stack.Increment_Last;
      Scope_Stack.Table (Scope_Stack.Last) :=
        Scope_Record'(Entity     => E,
                      Is_Body    => Is_Body,
                      Is_Logic   => False);
   end Push_Scope;

   ------------------------------
   -- Safe_Instantiation_Depth --
   ------------------------------

   function Safe_Instantiation_Depth (Id : Unique_Entity_Id) return Int
   is
      S : constant Source_Ptr := Sloc (+Id);
   begin
      if S /= Standard_ASCII_Location then
         return Instantiation_Depth (S);
      else
         return 0;
      end if;
   end Safe_Instantiation_Depth;

   -----------------------------
   -- Create_Alfa_Output_File --
   -----------------------------

   procedure Create_Alfa_Output_File (Filename : String) is
   begin
      Create (Output_File, Out_File, Filename);
   end Create_Alfa_Output_File;

end Alfa.Definition;
