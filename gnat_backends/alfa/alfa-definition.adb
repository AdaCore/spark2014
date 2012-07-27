------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                       A L F A . D E F I N I T I O N                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                        Copyright (C) 2011-2012, AdaCore                  --
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
with Ada.Strings.Fixed;
with Ada.Strings.Maps.Constants;

with AA_Util;               use AA_Util;
with Alloc;                 use Alloc;
with Atree;                 use Atree;
with Debug;
with Einfo;                 use Einfo;
with Errout;                use Errout;
with Namet;                 use Namet;
with Nlists;                use Nlists;
with Sem_Util;              use Sem_Util;
with Sinfo;                 use Sinfo;
with Sinput;                use Sinput;
with Snames;                use Snames;
with Stand;                 use Stand;
with Table;

with Alfa_Violations;       use all type Alfa_Violations.Vkind;

with Alfa.Frame_Conditions; use Alfa.Frame_Conditions;
with Alfa.Util;             use Alfa.Util;

package body Alfa.Definition is

   ---------------------
   -- Local Constants --
   ---------------------

   Name_GNATprove : constant String := "gnatprove";

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

      S_Short_Float         => True,
      S_Float               => True,
      S_Long_Float          => True,
      S_Long_Long_Float     => True,

      S_Character           => True,
      S_Wide_Character      => True,
      S_Wide_Wide_Character => True,

      S_String              => True,
      S_Wide_String         => True,
      S_Wide_Wide_String    => True,

      S_Duration            => True);

   ------------------
   -- Global State --
   ------------------

   During_Marking : Boolean := False;
   --  Flag set during marking of entities

   Output_File : Ada.Text_IO.File_Type;
   --  <file>.alfa in which this pass generates information about subprograms
   --  in Alfa and subprograms not in Alfa.

   Current_Unit_Is_Main_Body : Boolean;
   --  Flag set when marking the body for the current compiled unit

   Current_Unit_Is_Main_Spec : Boolean;
   --  Flag set when marking the spec for the current compiled unit

   Formal_Proof_On : Node_Sets.Set;
   --  Flag set after "Pragma Annotate (GNATprove, Force)"

   Formal_Proof_Off : Node_Sets.Set;
   --  Flag set after "Pragma Annotate (GNATprove, Disable)"

   type Violations is array (Alfa_Violations.Vkind) of Node_Sets.Set;

   Spec_Violations : Violations;
   --  Sets of entities which violate Alfa restrictions, per violation kind

   Body_Violations : Violations;
   --  Sets of subprogram entities whose body violate Alfa restrictions, per
   --  violation kind.

   Entities_In_Alfa : Node_Sets.Set;
   --  Entities in Alfa. An entity is inserted in this set if, after marking,
   --  no violations where attached to the corresponding scope. Standard
   --  entities are individually added to this set.

   Bodies_In_Alfa   : Node_Sets.Set;
   --  Subprogram entities whose body is in Alfa. An entity is inserted in this
   --  set if, after marking, no violations where attached to the corresponding
   --  body scope.

   -----------------
   -- Scope Stack --
   -----------------

   --  A stack of scopes records scopes currently open. The entity
   --  referenced can be:
   --  . a package
   --  . a subprogram
   --  . a variable
   --  . a type

   package Scope_Stack is

      --  Scopes for entities being marked. Is_Logic is True for all constructs
      --  which need to be translated to terms and propositions in Why3:
      --  assertions, preconditions, postconditions, and initialization
      --  expressions of constants. Is_Body is True for a package/subprogram
      --  body.
      type Scope_Record (Is_Logic : Boolean := False) is record
         case Is_Logic is
            when False =>
               Entity  : Entity_Id;
               Is_Body : Boolean;
            when True =>
               null;
         end case;
      end record;

      function Current_Scope return Scope_Record;
      --  Return the top-most scope

      procedure Pop_Scope (E : Entity_Id);
      --  Remove the top scope in the stack, which should match with entity E

      procedure Push_Scope (E : Entity_Id; Is_Body : Boolean := False);
      --  Set entity S as the top scope in the stack

      procedure Push_Logic_Scope;
      --  Push a logic scope as the top scope in the stack

      procedure Pop_Logic_Scope;
      --  Remove the top scope in the stack, which should be a logic scope

      function In_Logic_Scope return Boolean;
      --  Return whether the top scope in the stack is a logic scope

      function Formal_Proof_Currently_Disabled return Boolean;
      --  Determine the most top-level scope to have formal proof forced or
      --  disabled, and return True if formal proof is disabled. Return False
      --  in all other cases.

      function Formal_Proof_Currently_Forced return Boolean;
      --  Determine the most top-level scope to have formal proof forced or
      --  disabled, and return True if formal proof is forced. Return False
      --  in all other cases. This is useful to notify the user about Alfa
      --  violations in a scope where formal proof is forced.

      generic
         with procedure Iterator (S : Scope_Record);
      procedure Iterate;
      --  Iterate procedure Iterator over scopes of the stack

   end Scope_Stack;

   use Scope_Stack;

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Mark (N : Node_Id);
   --  Generic procedure for marking code

   --  Special treatment for marking some kinds of nodes

   procedure Mark_Attribute_Reference         (N : Node_Id);
   procedure Mark_Binary_Op                   (N : Node_Id);
   procedure Mark_Call                        (N : Node_Id);
   procedure Mark_Component_Declaration       (N : Node_Id);
   procedure Mark_Conditional_Expression      (N : Node_Id);
   procedure Mark_Handled_Statements          (N : Node_Id);
   procedure Mark_Identifier_Or_Expanded_Name (N : Node_Id);
   procedure Mark_If_Statement                (N : Node_Id);
   procedure Mark_Iteration_Scheme            (N : Node_Id);
   procedure Mark_Number_Declaration          (N : Node_Id);
   procedure Mark_Object_Declaration          (N : Node_Id);
   procedure Mark_Package_Body                (N : Node_Id);
   procedure Mark_Package_Declaration         (N : Node_Id);
   procedure Mark_Pragma                      (N : Node_Id);
   procedure Mark_Simple_Return_Statement     (N : Node_Id);
   procedure Mark_Subprogram_Body             (N : Node_Id);
   procedure Mark_Subprogram_Declaration      (N : Node_Id);
   procedure Mark_Subtype_Indication          (N : Node_Id);
   procedure Mark_Type_Conversion             (N : Node_Id);
   procedure Mark_Unary_Op                    (N : Node_Id);

   procedure Mark_Type_Entity (Id : Entity_Id; In_Container : Boolean);
   --  Types are special, we represent them by entities. In_Container is True
   --  for a type defined in a formal container package instance, which should
   --  be marked in Alfa or not, but not translated into Why3.

   procedure Mark_Actions (N : Node_Id; L : List_Id);
   --  Mark a possibly null list of actions L from expression N. It should be
   --  called before the expression to which the actions apply is marked, so
   --  that declarations of constants in actions are possibly marked in Alfa.

   procedure Mark_List (L : List_Id);
   --  Call Mark on all nodes in list L

   procedure Mark_Most_Underlying_Type_In_Alfa (Id : Entity_Id; N : Node_Id);
   --  The most underlying type for type Id should be in Alfa, otherwise mark
   --  node N as not in Alfa.

   procedure Mark_Violation
     (Msg : String;
      N   : Node_Id;
      V   : Alfa_Violations.Vkind);
   --  Mark node N as a violation of Alfa. The violation is attached to all
   --  entities in the current scope stack. A message is also issued in some
   --  cases.

   procedure Mark_Violation
     (Msg  : String;
      N    : Node_Id;
      From : Entity_Id);
   --  Similar to the previous one, except here violations are inherited from
   --  entity From.

   generic
      with procedure Mark_Body_Violations (E : Entity_Id) is <>;
      with procedure Mark_Spec_Violations (E : Entity_Id) is <>;
   procedure Mark_Violations_For_All_Scopes;
   --  Helper procedure used in Mark_Violation

   procedure Inherit_Violations
     (A        : in out Violations;
      To, From : Entity_Id);
   --  Make To inherit the violations of From in Violations

   function Has_Violations (Id : Entity_Id) return Boolean;
   --  Return whether a violation of Alfa was detected while analyzing the
   --  definition of entity Id. This does not include violations in the body of
   --  a subprogram, which are recorded separately.

   function Has_Body_Violations (Id : Entity_Id) return Boolean;
   --  Return whether a violation of Alfa was detected while analyzing the body
   --  of subprogram Id.

   function Force_Alfa (N : Node_Id) return Boolean;
   --  Return whether Alfa rules should be enforced in the current scope,
   --  either because option -gnatd.K or -gnatd.E was passed to gnat2why (which
   --  only applies to user source code), or because the current scope is
   --  forcing formal proof.

   function Complete_Error_Msg
     (Msg : String;
      V   : Alfa_Violations.Vkind) return String;
   --  Generate a message for Alfa violations, which may be an error, a warning
   --  or an info message depending on the analysis mode and the violation.

   procedure Generate_Output_In_Out_Alfa (Id : Entity_Id);
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

   -------------------
   -- After_Marking --
   -------------------

   procedure After_Marking is
   begin
      Close (Output_File);
      During_Marking := False;
   end After_Marking;

   --------------------
   -- Before_Marking --
   --------------------

   procedure Before_Marking (Filename : String) is
   begin
      Create (Output_File, Out_File, Filename);
      During_Marking := True;
   end Before_Marking;

   ------------------
   -- Body_In_Alfa --
   ------------------

   function Body_In_Alfa (Id : Entity_Id) return Boolean is
   begin
      return Bodies_In_Alfa.Contains (Id);
   end Body_In_Alfa;

   ------------------------
   -- Complete_Error_Msg --
   ------------------------

   function Complete_Error_Msg
     (Msg : String;
      V   : Alfa_Violations.Vkind) return String
   is
      --  When reporting a forward reference, this takes priority over the
      --  default reason for not being in Alfa (e.g. "subprogram called")

      Use_Msg : constant String :=
                  (if V = NIR_Forward_Reference then
                     "forward reference"
                   else Msg);
   begin
      case V is
         when Alfa_Violations.Not_In_Roadmap =>

            --  In mode 'detect', only issue a warning when a construct is not
            --  in Alfa.

            if Debug.Debug_Flag_Dot_KK then
               return Use_Msg & "? is not in Alfa";
            else
               return Use_Msg & " is not in Alfa";
            end if;

         when Alfa_Violations.Not_Yet_Implemented =>

            --  In mode 'detect', only issue an info message when a construct
            --  is not yet supported.

            if Debug.Debug_Flag_Dot_KK then
               return "?info: " & Use_Msg & " is not yet supported";
            else
               return Use_Msg & "? is not yet supported";
            end if;
      end case;
   end Complete_Error_Msg;

   ----------------
   -- Force_Alfa --
   ----------------

   function Force_Alfa (N : Node_Id) return Boolean is
     (((Debug.Debug_Flag_Dot_KK
         or else Debug.Debug_Flag_Dot_EE)
        and then (In_Main_Unit_Spec (N)
                   or else In_Main_Unit_Body (N)))
       or else
         Formal_Proof_Currently_Forced);

   ---------------------------------
   -- Generate_Output_In_Out_Alfa --
   ---------------------------------

   procedure Generate_Output_In_Out_Alfa (Id : Entity_Id) is
      generic
         type Violation_Subkind is (<>);
         Open, Close : Character;
         with function Has_Violation
           (V : Violation_Subkind;
            E : Entity_Id) return Boolean is <>;
         with function Get_Violation_Msg
           (V : Violation_Subkind) return Unbounded_String is <>;
      function Collect_Msg_Violations
        (E : Entity_Id) return String;
      --  Produce a comma-separated list of message for NYI or NIR violations,
      --  enclosed in Open-Close characters.

      function Suffix return String;
      --  Suffix string indicates why subprogram body is not in Alfa

      ----------------------
      -- Helper Functions --
      ----------------------

      function Has_Violation
        (V : Alfa_Violations.Vkind;
         E : Entity_Id) return Boolean
      is
        (Body_Violations (V).Contains (E));

      function Get_Violation_Msg
        (V : Alfa_Violations.Vkind) return Unbounded_String
      is
        (Alfa_Violations.Violation_Msg (V));

      function Location return String is
        (Name_String (Chars (Id)) & ' ' & Build_Location_String (Sloc (Id)));
      --  Location string points to source location for entity. Use the
      --  location of the body (Defining_Entity) rather than the location
      --  of the spec (Id).

      ----------------------------
      -- Collect_Msg_Violations --
      ----------------------------

      function Collect_Msg_Violations
        (E : Entity_Id) return String
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
         if Body_In_Alfa (Id) then
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
      if Comes_From_Source (Id) then
         if Body_In_Alfa (Id) then
            C1 := '+';
         elsif (for some V in Alfa_Violations.Not_In_Roadmap =>
                   Body_Violations (V).Contains (Id)) then
            C1 := '-';
         else
            C1 := '*';
         end if;

         if In_Alfa (Id) then
            C2 := '+';
         elsif (for some V in Alfa_Violations.Not_In_Roadmap =>
                   Spec_Violations (V).Contains (Id)) then
            C2 := '-';
         else
            C2 := '*';
         end if;

         Put_Line (Output_File, C1 & C2 & ' ' & Location & Suffix);
      end if;
   end Generate_Output_In_Out_Alfa;

   -------------------------
   -- Has_Body_Violations --
   -------------------------

   function Has_Body_Violations (Id : Entity_Id) return Boolean is
     (for some S of Body_Violations => S.Contains (Id));

   --------------------
   -- Has_Violations --
   --------------------

   function Has_Violations (Id : Entity_Id) return Boolean is
     (for some S of Spec_Violations => S.Contains (Id));

   -------------
   -- In_Alfa --
   -------------

   function In_Alfa (Id : Entity_Id) return Boolean is
   begin
      --  Type might not have been marked yet, in case it is an Itype or a
      --  class-wide type.

      if During_Marking
        and then (Is_Itype (Id)
                   or else Ekind (Id) = E_Class_Wide_Type)
      then
         Mark_Type_Entity (Id, In_Container => False);
      end if;

      return Entities_In_Alfa.Contains (Id);
   end In_Alfa;

   ------------------------
   -- Inherit_Violations --
   ------------------------

   procedure Inherit_Violations
     (A        : in out Violations;
      To, From : Entity_Id)
   is
   begin
      --  If From was explicitly marked as not in Alfa, inherit the reason for
      --  not being in Alfa.

      if (for some S of Spec_Violations => S.Contains (From)) then
         for V in Alfa_Violations.Vkind loop
            if Spec_Violations (V).Contains (From) then
               A (V).Include (To);
            end if;
         end loop;

      --  If From was not yet marked, this is a forward reference (or currently
      --  an entity defined in a task, which is not marked, to be refined
      --  later.)

      else
         pragma Assert (not All_Entities.Contains (From));
         A (NIR_Forward_Reference).Include (To);
      end if;
   end Inherit_Violations;

   ----------
   -- Mark --
   ----------

   procedure Mark (N : Node_Id) is
   begin
      --  If present, the type of N should be in Alfa. This also allows marking
      --  Itypes and class-wide types at their first occurrence (inside
      --  In_Alfa).

      if Nkind (N) in N_Has_Etype
        and then not In_Alfa (Etype (N))
      then
         Mark_Violation ("type used", N, From => Etype (N));
      end if;

      --  Dispatch on node kind

      case Nkind (N) is

         when N_Abstract_Subprogram_Declaration =>
            Mark_Violation ("abstract subprogram", N, NYI_Tagged);

         when N_Aggregate =>

            --  In logic scopes, aggregates should be completely initialized to
            --  be in Alfa, otherwise they do not have a logic interpretation.

            if In_Logic_Scope
              and then not Aggregate_Is_Fully_Initialized (N)
            then
               Mark_Violation ("aggregate in logic not fully initialized",
                               N, NIR_Uninit_Logic_Expr);
            end if;

            Mark_Most_Underlying_Type_In_Alfa (Etype (N), N);
            Mark_List (Expressions (N));
            Mark_List (Component_Associations (N));

         when N_Allocator =>
            Mark_Violation ("allocator", N, NIR_Dynamic_Alloc);

         when N_Assignment_Statement =>
            Mark (Name (N));
            Mark (Expression (N));

         when N_At_Clause =>
            Mark_Violation ("at clause", N, NYI_Rep_Clause);

         when N_Attribute_Reference =>
            Mark_Attribute_Reference (N);

         when N_Attribute_Definition_Clause   =>
            Mark_Violation ("attribute definition clause", N, NYI_Rep_Clause);

         when N_Binary_Op =>
            Mark_Binary_Op (N);

         when N_Block_Statement =>
            Mark_List (Declarations (N));
            Mark (Handled_Statement_Sequence (N));

         when N_Case_Expression |
              N_Case_Statement  =>
            Mark (Expression (N));
            Mark_List (Alternatives (N));

         when N_Case_Expression_Alternative =>
            Mark_Actions (N, Actions (N));
            Mark (Expression (N));

         when N_Case_Statement_Alternative =>
            Mark_List (Statements (N));

         when N_Code_Statement =>
            Mark_Violation ("code statement", N, NIR_Assembly_Lang);

         when N_Component_Association =>
            pragma Assert (No (Loop_Actions (N)));
            Mark_List (Choices (N));
            if not Box_Present (N) then
               Mark (Expression (N));
            end if;

         when N_Component_Declaration =>
            Mark_Component_Declaration (N);

         when N_Conditional_Expression =>
            Mark_Conditional_Expression (N);

         when N_Enumeration_Representation_Clause =>
            Mark_Violation
              ("enumeration representation clause", N, NYI_Rep_Clause);

         when N_Exception_Declaration          |
              N_Exception_Renaming_Declaration =>
            Mark_Violation ("exception", N, NIR_Exception);

         when N_Exit_Statement =>
            if Present (Condition (N)) then
               Mark (Condition (N));
            end if;

         when N_Expanded_Name =>
            Mark_Identifier_Or_Expanded_Name (N);

         when N_Explicit_Dereference =>
            Mark_Violation ("explicit dereference", N, NIR_Access);

         when N_Extended_Return_Statement =>
            Mark_Violation ("extended RETURN", N, NYI_Extended_Return);

         when N_Extension_Aggregate =>
            Mark_Violation ("extension aggregate", N, NYI_Aggregate);

         when N_Free_Statement =>
            Mark_Violation ("free statement", N, NIR_Dealloc);

         when N_Function_Call =>
            Mark_Call (N);

         when N_Goto_Statement =>
            Mark_Violation ("goto statement", N, NIR_Goto);

         when N_Handled_Sequence_Of_Statements =>
            Mark_Handled_Statements (N);

         when N_Identifier =>
            Mark_Identifier_Or_Expanded_Name (N);

         when N_If_Statement =>
            Mark_If_Statement (N);

         when N_Indexed_Component =>
            Mark_Most_Underlying_Type_In_Alfa (Etype (Prefix (N)), N);
            Mark (Prefix (N));
            Mark_List (Expressions (N));

         when N_Iterator_Specification =>
            if Present (Subtype_Indication (N)) then
               Mark (Subtype_Indication (N));
            end if;

            --  Treat specially the case of X.Iterate for X a formal container,
            --  so that the iterator type is ignored instead of being
            --  identified as a violation of Alfa.

            declare
               Iter : constant Node_Id := Name (N);
            begin
               if Nkind (Iter) = N_Function_Call
                 and then Is_Entity_Name (Name (Iter))
                 and then
                   Ada.Strings.Fixed.Translate
                     (Get_Name_String (Chars (Name (Iter))),
                      Ada.Strings.Maps.Constants.Lower_Case_Map) =
                   Alfa.Util.Lowercase_Iterate_Name
                 and then
                   Location_In_Formal_Containers (Sloc (Entity (Name (Iter))))
               then
                  Mark_List (Parameter_Associations (Iter));
               else
                  Mark (Name (N));
               end if;
            end;

         when N_Loop_Statement =>
            if Present (Iteration_Scheme (N)) then
               Mark_Iteration_Scheme (Iteration_Scheme (N));
            end if;
            Mark_List (Statements (N));

         --  Expansion rewrites complex membership tests into simpler ones

         when N_Membership_Test =>
            pragma Assert (No (Alternatives (N)));
            Mark (Left_Opnd (N));
            Mark (Right_Opnd (N));

         when N_Null =>
            Mark_Violation ("null", N, NIR_Access);

         when N_Number_Declaration =>
            Mark_Number_Declaration (N);

         when N_Object_Declaration =>
            Mark_Object_Declaration (N);

         when N_Package_Body =>
            Mark_Package_Body (N);

         when N_Package_Body_Stub =>
            Mark_Package_Body (Get_Body_From_Stub (N));

         when N_Package_Declaration =>
            Mark_Package_Declaration (N);

         when N_Parameter_Association =>
            Mark (Explicit_Actual_Parameter (N));

         when N_Pragma =>
            Mark_Pragma (N);

         when N_Procedure_Call_Statement =>
            Mark_Call (N);

         when N_Qualified_Expression =>
            Mark (Subtype_Mark (N));
            Mark (Expression (N));

         when N_Quantified_Expression =>
            if Present (Loop_Parameter_Specification (N)) then
               Mark (Discrete_Subtype_Definition
                      (Loop_Parameter_Specification (N)));
            else
               Mark (Iterator_Specification (N));
            end if;
            Mark (Condition (N));

         when N_Raise_Statement |
              N_Raise_xxx_Error =>
            Mark_Violation ("raise statement", N, NIR_Exception);

         when N_Range =>
            Mark (Low_Bound (N));
            Mark (High_Bound (N));

         --  Make sure the original node for a real literal is in Alfa, because
         --  the translation uses the original node if the node was rewritten.

         when N_Real_Literal =>
            if Is_Rewrite_Substitution (N) then
               Mark (Original_Node (N));
            end if;

         when N_Record_Representation_Clause =>
            Mark_Violation ("record representation clause", N, NYI_Rep_Clause);

         when N_Reference =>
            Mark_Violation ("reference", N, NIR_Access);

         when N_Short_Circuit =>
            Mark_Actions (N, Actions (N));
            Mark (Left_Opnd (N));
            Mark (Right_Opnd (N));

         when N_Simple_Return_Statement =>
            Mark_Simple_Return_Statement (N);

         when N_Selected_Component =>
            Mark_Most_Underlying_Type_In_Alfa (Etype (Prefix (N)), N);
            Mark (Prefix (N));
            Mark (Selector_Name (N));

         when N_Slice =>
            Mark_Most_Underlying_Type_In_Alfa (Etype (Prefix (N)), N);

         when N_Subprogram_Body =>

            --  For expression functions that have a unique declaration, the
            --  body inserted by the frontend may be far from the original
            --  point of declaration, after the private declarations of the
            --  package (to avoid premature freezing.) In those cases, mark the
            --  subprogram body at the same point as the subprogram
            --  declaration, so that entities declared afterwards have access
            --  to the axiom defining the expression function.

            if Present (Get_Expression_Function (Unique_Defining_Entity (N)))
              and then not Comes_From_Source (Original_Node (N))
            then
               null;
            else
               if Acts_As_Spec (N) then
                  Mark_Subprogram_Declaration (N);
               end if;
               Mark_Subprogram_Body (N);
            end if;

         when N_Subprogram_Body_Stub =>
            if Is_Subprogram_Stub_Without_Prior_Declaration (N) then
               Mark_Subprogram_Declaration (N);
            end if;
            Mark_Subprogram_Body (Get_Body_From_Stub (N));

         when N_Subprogram_Declaration =>
            Mark_Subprogram_Declaration (N);

            --  For expression functions that have a unique declaration, the
            --  body inserted by the frontend may be far from the original
            --  point of declaration, after the private declarations of the
            --  package (to avoid premature freezing.) In those cases, mark the
            --  subprogram body at the same point as the subprogram
            --  declaration, so that entities declared afterwards have access
            --  to the axiom defining the expression function.

            declare
               E      : constant Entity_Id := Defining_Entity (N);
               Body_N : constant Node_Id := Alfa.Util.Get_Subprogram_Body (E);
            begin
               if Present (Get_Expression_Function (E))
                 and then not Comes_From_Source (Original_Node (Body_N))
               then
                  Mark_Subprogram_Body (Body_N);
               end if;
            end;

         when N_Subtype_Indication =>
            Mark_Subtype_Indication (N);

         when N_Type_Conversion =>
            Mark_Type_Conversion (N);

         when N_Unary_Op =>
            Mark_Unary_Op (N);

         when N_Unchecked_Expression =>
            Mark_Violation ("unchecked expression", N, NYI_Unchecked);

         when N_Unchecked_Type_Conversion =>
            if Comes_From_Source (N) then
               Mark_Violation
                 ("unchecked type conversion", N, NIR_Unchecked_Conv);
            else
               Mark (Expression (N));
            end if;

         when N_Validate_Unchecked_Conversion =>
            Mark_Violation ("unchecked conversion", N, NIR_Unchecked_Conv);

         when N_Variant_Part =>
            declare
               Var : Node_Id := First (Variants (N));
            begin
               while Present (Var) loop
                  Mark (Var);
                  Next (Var);
               end loop;
            end;

         --  Frontend sometimes declares an Itype for the base type of a type
         --  declaration. This Itype should be marked at the point of
         --  declaration of the corresponding type, otherwise it may end up
         --  being marked multiple times in various client units, which leads
         --  to multiple definitions in Why3 for the same type.

         when N_Full_Type_Declaration         |
              N_Private_Extension_Declaration |
              N_Private_Type_Declaration      |
              N_Protected_Type_Declaration    |
              N_Subtype_Declaration           |
              N_Task_Type_Declaration         =>
            declare
               T  : constant Entity_Id := Defining_Identifier (N);
               BT : constant Entity_Id := Base_Type (T);
            begin
               Mark_Type_Entity (T, In_Container => False);
               if Is_Itype (BT) then
                  Mark_Type_Entity (BT, In_Container => False);
               end if;
            end;

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
            Mark_Violation ("tasking", N, NIR_Tasking);

         --  The following kinds can be safely ignored by marking

         when N_Character_Literal                      |
              N_Formal_Object_Declaration              |
              N_Formal_Package_Declaration             |
              N_Formal_Subprogram_Declaration          |
              N_Formal_Type_Declaration                |
              N_Freeze_Entity                          |
              N_Function_Instantiation                 |
              N_Generic_Function_Renaming_Declaration  |
              N_Generic_Package_Declaration            |
              N_Generic_Package_Renaming_Declaration   |
              N_Generic_Procedure_Renaming_Declaration |
              N_Generic_Subprogram_Declaration         |
              N_Implicit_Label_Declaration             |
              N_Incomplete_Type_Declaration            |
              N_Integer_Literal                        |
              N_Itype_Reference                        |
              N_Label                                  |
              N_Null_Statement                         |
              N_Operator_Symbol                        |
              N_Others_Choice                          |
              N_Package_Instantiation                  |
              N_Package_Renaming_Declaration           |
              N_Procedure_Instantiation                |
              N_String_Literal                         |
              N_Subprogram_Info                        |
              N_Subprogram_Renaming_Declaration        |
              N_Use_Package_Clause                     |
              N_With_Clause                            |
              N_Use_Type_Clause                        =>
            null;

         --  Object renamings are rewritten by expansion, but they are kept in
         --  the tree, so just ignore them.

         when N_Object_Renaming_Declaration =>
            null;

         --  The following kinds are rewritten by expansion

         when N_Expression_Function =>
            raise Program_Error;

         --  The following kind is never generated in Alfa mode

         when N_Expression_With_Actions =>
            raise Program_Error;

         --  Mark should not be called on other kinds

         when
              N_Abortable_Part |
              N_Accept_Alternative |
              N_Access_Definition |
              N_Access_Function_Definition |
              N_Access_Procedure_Definition |
              N_Access_To_Object_Definition |
              N_Aspect_Specification |
              N_Compilation_Unit |
              N_Compilation_Unit_Aux |
              N_Component_Clause |
              N_Component_Definition |
              N_Component_List |
              N_Constrained_Array_Definition  |
              N_Contract |
              N_Decimal_Fixed_Point_Definition |
              N_Defining_Character_Literal |
              N_Defining_Identifier |
              N_Defining_Operator_Symbol |
              N_Defining_Program_Unit_Name |
              N_Delay_Alternative |
              N_Delta_Constraint |
              N_Derived_Type_Definition |
              N_Designator |
              N_Digits_Constraint |
              N_Discriminant_Association |
              N_Discriminant_Specification |
              N_Function_Specification |
              N_Iteration_Scheme |
              N_Loop_Parameter_Specification |
              N_Elsif_Part |
              N_Empty |
              N_Entry_Body_Formal_Part |
              N_Enumeration_Type_Definition |
              N_Entry_Call_Alternative |
              N_Entry_Index_Specification |
              N_Error |
              N_Exception_Handler |
              N_Floating_Point_Definition |
              N_Formal_Decimal_Fixed_Point_Definition |
              N_Formal_Derived_Type_Definition |
              N_Formal_Discrete_Type_Definition |
              N_Formal_Floating_Point_Definition |
              N_Formal_Incomplete_Type_Definition |
              N_Formal_Modular_Type_Definition |
              N_Formal_Ordinary_Fixed_Point_Definition |
              N_Formal_Private_Type_Definition |
              N_Formal_Signed_Integer_Type_Definition |
              N_Generic_Association |
              N_Index_Or_Discriminant_Constraint |
              N_Mod_Clause |
              N_Modular_Type_Definition |
              N_Ordinary_Fixed_Point_Definition |
              N_Parameter_Specification |
              N_Pragma_Argument_Association |
              N_Package_Specification |
              N_Procedure_Specification |
              N_Protected_Definition |
              N_Push_Pop_xxx_Label |
              N_Range_Constraint |
              N_Real_Range_Specification |
              N_Record_Definition |
              N_SCIL_Dispatch_Table_Tag_Init |
              N_SCIL_Dispatching_Call |
              N_SCIL_Membership_Test |
              N_Signed_Integer_Type_Definition |
              N_Single_Protected_Declaration |
              N_Subunit |
              N_Task_Definition |
              N_Terminate_Alternative |
              N_Triggering_Alternative |
              N_Unconstrained_Array_Definition  |
              N_Unused_At_Start |
              N_Unused_At_End |
              N_Variant =>
            raise Program_Error;
      end case;
   end Mark;

   ------------------
   -- Mark_Actions --
   ------------------

   procedure Mark_Actions (N : Node_Id; L : List_Id) is
      function Acceptable_Actions (L : List_Id) return Boolean;
      --  Return whether L is a list of acceptable actions, which can be
      --  translated into Why.

      ------------------------
      -- Acceptable_Actions --
      ------------------------

      function Acceptable_Actions (L : List_Id) return Boolean is
         N : Node_Id;

      begin
         N := First (L);
         while Present (N) loop
            --  Only actions that consist in N_Object_Declaration nodes for
            --  constants are translated.

            if Nkind (N) /= N_Object_Declaration
              or else not Constant_Present (N)
            then
               return False;
            end if;

            Next (N);
         end loop;

         return True;
      end Acceptable_Actions;

   begin
      if Present (L) then
         Mark_List (L);
         if not Acceptable_Actions (L) then
            Mark_Violation ("expression with action", N, NYI_Expr_With_Action);
         end if;
      end if;
   end Mark_Actions;

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
         when Attribute_Ceiling    |
              Attribute_First      |
              Attribute_Floor      |
              Attribute_Image      |
              Attribute_Last       |
              Attribute_Length     |
              Attribute_Mod        |
              Attribute_Modulus    |
              Attribute_Old        |
              Attribute_Pos        |
              Attribute_Pred       |
              Attribute_Range      |
              Attribute_Result     |
              Attribute_Rounding   |
              Attribute_Truncation |
              Attribute_Succ       |
              Attribute_Val        |
              Attribute_Value      |
              Attribute_Min        |
              Attribute_Max        =>
            null;

         when others =>
            Mark_Violation ("attribute", N, NYI_Attribute);
            return;
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
            Mark_Violation ("concatenation", N, NYI_Concatenation);

         when N_Op_Lt | N_Op_Le | N_Op_Gt | N_Op_Ge =>
            if Is_Array_Type (Left_T) then
               Mark_Violation
                 ("ordering operator on array type", N, NYI_Array_Operation);
            end if;

         when N_Op_Eq | N_Op_Ne | N_Op_Expon =>
            null;

         when N_Op_And | N_Op_Or | N_Op_Xor =>
            if not Is_Boolean_Type (Etype (N)) then
               Mark_Violation
                 ("bitwise modular operation", N, NYI_Arith_Operation);
            elsif Is_Array_Type (Left_T)
              and then Nkind (N) in N_Binary_Op
            then
               Mark_Violation
                 ("binary operator on array type", N, NYI_Array_Operation);
            end if;

         --  Issue a warning whenever an arithmetic operation could be
         --  reordered by the compiler, like "A + B - C", as a given
         --  ordering may overflow and another may not. Not that a warning is
         --  issued even on operations like "A * B / C" which are not reordered
         --  by GNAT, as they could be reordered according to RM 4.5/13.

         when N_Op_Add | N_Op_Subtract =>
            if Nkind_In (Left_Opnd (N), N_Op_Add, N_Op_Subtract)
              and then Paren_Count (Left_Opnd (N)) = 0
            then
               Error_Msg_F
                 ("?possible re-ordering due to missing parentheses",
                  Left_Opnd (N));
            end if;

            if Nkind_In (Right_Opnd (N), N_Op_Add, N_Op_Subtract)
              and then Paren_Count (Right_Opnd (N)) = 0
            then
               Error_Msg_F
                 ("?possible re-ordering due to missing parentheses",
                  Right_Opnd (N));
            end if;

         when N_Op_Multiply | N_Op_Divide | N_Op_Mod | N_Op_Rem =>
            if Nkind (Left_Opnd (N)) in N_Multiplying_Operator
              and then Paren_Count (Left_Opnd (N)) = 0
            then
               Error_Msg_F
                 ("?possible re-ordering due to missing parentheses",
                  Left_Opnd (N));
            end if;

            if Nkind (Right_Opnd (N)) in N_Multiplying_Operator
              and then Paren_Count (Right_Opnd (N)) = 0
            then
               Error_Msg_F
                 ("?possible re-ordering due to missing parentheses",
                  Right_Opnd (N));
            end if;

         when N_Op_Shift =>
            Mark_Violation ("operator", N, NYI_Arith_Operation);
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

      if not Is_Entity_Name (Nam)
        or else No (Entity (Nam))
      then
         Mark_Violation ("call", N, NIR_Indirect_Call);

      elsif not In_Alfa (Entity (Nam)) then
         Mark_Violation ("subprogram called", N, From => Entity (Nam));
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

      Push_Scope (Standard_Standard);

      Current_Unit_Is_Main_Body := In_Main_Unit_Body (N);
      Current_Unit_Is_Main_Spec := In_Main_Unit_Spec (N);

      Context_N := First (Context_Items (CU));
      while Present (Context_N) loop
         Mark (Context_N);
         Next (Context_N);
      end loop;

      Mark (N);
      Pop_Scope (Standard_Standard);
   end Mark_Compilation_Unit;

   --------------------------------
   -- Mark_Component_Declaration --
   --------------------------------

   procedure Mark_Component_Declaration (N : Node_Id) is
      Def : constant Node_Id   := Component_Definition (N);

   begin
      if Aliased_Present (Def) then
         Mark_Violation ("ALIASED", N, NIR_Access);
      end if;

      if Present (Access_Definition (Def)) then
         Mark_Violation ("access type", Def, NIR_Access);
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
      Mark_Actions (N, Then_Actions (N));
      Mark_Actions (N, Else_Actions (N));

      Else_Expr := Next (Then_Expr);

      Mark (Condition);
      Mark (Then_Expr);

      if Present (Else_Expr) then
         Mark (Else_Expr);
      end if;
   end Mark_Conditional_Expression;

   -----------------------------
   -- Mark_Handled_Statements --
   -----------------------------

   procedure Mark_Handled_Statements (N : Node_Id) is
      Handlers : constant List_Id := Exception_Handlers (N);

   begin
      if Present (Handlers) then
         Mark_Violation ("handler", First (Handlers), NIR_Exception);
      end if;

      Mark_List (Statements (N));
   end Mark_Handled_Statements;

   --------------------------------------
   -- Mark_Identifier_Or_Expanded_Name --
   --------------------------------------

   procedure Mark_Identifier_Or_Expanded_Name (N : Node_Id) is
      E : Entity_Id;
   begin
      if Is_Entity_Name (N) and then Present (Entity (N)) then
         E := Entity (N);

         case Ekind (E) is
            when Object_Kind =>
               if (Ekind_In (E, E_Variable, E_Constant)
                    or else Ekind (E) in Formal_Kind)
                 and then not (In_Alfa (Entity (N)))
               then
                  Mark_Violation ("object", N, From => Entity (N));
               end if;

            when Named_Kind =>
               if not (In_Alfa (Entity (N))) then
                  Mark_Violation ("object", N, From => Entity (N));
               end if;

            when Type_Kind =>
               if not In_Alfa (Entity (N)) then
                  Mark_Violation ("type", N, From => Entity (N));
               end if;

            --  Subprogram name appears for example in Sub'Result

            when E_Void                  |
                 E_Enumeration_Literal   |
                 Subprogram_Kind         |
                 E_Block                 |
                 Generic_Subprogram_Kind |
                 E_Generic_Package       |
                 E_Label                 |
                 E_Loop                  |
                 E_Return_Statement      |
                 E_Package               |
                 E_Package_Body          |
                 E_Subprogram_Body       =>
               null;

            when E_Exception =>
               Mark_Violation ("exception", N, NIR_Exception);

            when E_Entry                 |
                 E_Entry_Family          |
                 E_Entry_Index_Parameter |
                 E_Protected_Object      |
                 E_Protected_Body        |
                 E_Task_Body             =>
               Mark_Violation ("tasking", N, NIR_Tasking);
         end case;
      end if;
   end Mark_Identifier_Or_Expanded_Name;

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
               Mark_Actions (N, Condition_Actions (Part));
               Mark (Condition (Part));
               Mark_List (Then_Statements (Part));
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
      if Present (Condition (N)) then
         Mark_Actions (N, Condition_Actions (N));
         Mark (Condition (N));

      elsif Present (Loop_Parameter_Specification (N)) then
         pragma Assert (No (Condition_Actions (N)));
         --  The entity for iterating over a loop is always in Alfa
         Mark (Discrete_Subtype_Definition
                 (Loop_Parameter_Specification (N)));

      else
         pragma Assert (No (Condition_Actions (N)));
         pragma Assert (Present (Iterator_Specification (N)));
         Mark_Violation ("loop with iterator", N, NYI_Iterators);
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

   procedure Mark_Violation
     (Msg    : String;
      N      : Node_Id;
      V      : Alfa_Violations.Vkind)
   is
      procedure Mark_Body_Violations (E : Entity_Id);
      procedure Mark_Spec_Violations (E : Entity_Id);

      procedure Mark_Body_Violations (E : Entity_Id) is
      begin
         Body_Violations (V).Include (E);
      end Mark_Body_Violations;

      procedure Mark_Spec_Violations (E : Entity_Id) is
      begin
         Spec_Violations (V).Include (E);
      end Mark_Spec_Violations;

      procedure Mark_All_Scopes is new Mark_Violations_For_All_Scopes;

   begin
      --  If formal proof is forced and node N is not compiler-generated, then
      --  notify the user about the violation.

      if Force_Alfa (N)
        and then Comes_From_Source (N)
      then
         Error_Msg_F (Complete_Error_Msg (Msg, V), N);
      end if;

      Mark_All_Scopes;
   end Mark_Violation;

   procedure Mark_Violation
     (Msg  : String;
      N    : Node_Id;
      From : Entity_Id)
   is
      procedure Mark_Body_Violations (E : Entity_Id);
      procedure Mark_Spec_Violations (E : Entity_Id);

      procedure Mark_Body_Violations (E : Entity_Id) is
      begin
         Inherit_Violations (Body_Violations, From => From, To => E);
      end Mark_Body_Violations;

      procedure Mark_Spec_Violations (E : Entity_Id) is
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
         if In_Standard_Scope (From)
           or else Spec_Violations (NIR_XXX).Contains (From)
         then
            Error_Msg_F (Complete_Error_Msg (Msg, NIR_XXX), N);

         elsif (for some V in Alfa_Violations.Not_In_Roadmap =>
                  Spec_Violations (V).Contains (From))
         then
            for V in Alfa_Violations.Not_In_Roadmap loop
               if Spec_Violations (V).Contains (From) then
                  Error_Msg_F (Complete_Error_Msg (Msg, V), N);
               end if;
            end loop;

         elsif (for some V in Alfa_Violations.Not_Yet_Implemented =>
                  Spec_Violations (V).Contains (From))
         then
            for V in Alfa_Violations.Not_Yet_Implemented loop
               if Spec_Violations (V).Contains (From) then
                  Error_Msg_F (Complete_Error_Msg (Msg, V), N);
               end if;
            end loop;

         else
            Error_Msg_F (Complete_Error_Msg (Msg, NIR_Forward_Reference), N);
         end if;
      end if;

      Mark_All_Scopes;
   end Mark_Violation;

   -----------------------------
   -- Mark_Number_Declaration --
   -----------------------------

   procedure Mark_Number_Declaration (N : Node_Id) is

      Id   : constant Entity_Id := Defining_Entity (N);
      Expr : constant Node_Id   := Expression (N);
      T    : constant Entity_Id := Etype (Id);

   begin
      --  The number declaration is in Alfa if-and-only-if its base type is
      --  in Alfa.

      Push_Scope (Id);

      if not In_Alfa (T) then
         Mark_Violation ("type", N, From => T);
      end if;

      if Present (Expr) then
         Mark (Expr);
      end if;

      Pop_Scope (Id);
   end Mark_Number_Declaration;

   -----------------------------
   -- Mark_Object_Declaration --
   -----------------------------

   procedure Mark_Object_Declaration (N : Node_Id) is
      Id   : constant Entity_Id := Defining_Entity (N);
      Def  : constant Node_Id   := Object_Definition (N);
      Expr : constant Node_Id   := Expression (N);
      T    : constant Entity_Id := Etype (Id);

      Deferred_Constant : constant Boolean :=
                            Ekind (Id) = E_Constant
                              and then Present (Full_View (Id));
   begin
      --  Mark completions of deferred constants, so that generation of Why can
      --  use this information.

      if Deferred_Constant then
         Add_Full_And_Partial_View (Full_View (Id), Id);
      end if;

      --  The object is in Alfa if-and-only-if its type is in Alfa, it is not
      --  aliased, and its initialization expression, if any, is in Alfa.

      Push_Scope (Id);

      if not In_Alfa (T) then
         Mark_Violation ("type", Def, From => T);
      end if;

      if Aliased_Present (N) then
         Mark_Violation ("ALIASED", N, NIR_Access);
      end if;

      if Present (Expr) then

         --  The initial value of a constant is treated as a logic expression,
         --  in order to translate it to a Why3 function later.

         if Ekind (Id) = E_Constant then
            Push_Logic_Scope;
         end if;

         Mark (Expr);

         if Ekind (Id) = E_Constant then
            Pop_Logic_Scope;
         end if;
      end if;

      Pop_Scope (Id);
   end Mark_Object_Declaration;

   -----------------------
   -- Mark_Package_Body --
   -----------------------

   procedure Mark_Package_Body (N : Node_Id) is
      Id     : constant Entity_Id := Unique_Defining_Entity (N);
      Decl_N : constant Node_Id   := Parent (Parent (Id));

   begin
      --  Do not analyze generic bodies

      if Ekind (Id) = E_Generic_Package then
         return;
      end if;

      --  Do not analyze bodies for instantiations of the formal containers

      if Is_Instantiation_Of_Formal_Container (Decl_N) then
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

      procedure Declare_In_Container (Decls : List_Id);
      --  Mark types and subprograms from formal container instantiations

      --------------------------
      -- Declare_In_Container --
      --------------------------

      procedure Declare_In_Container (Decls : List_Id) is
         Decl : Node_Id;
         Id   : Entity_Id;
      begin
         Decl := First (Decls);

         while Present (Decl) loop
            if Nkind (Decl) in N_Full_Type_Declaration         |
                               N_Private_Type_Declaration      |
                               N_Private_Extension_Declaration |
                               N_Subtype_Declaration           |
                               N_Subprogram_Declaration
            then
               Id := Defining_Entity (Decl);

               if Ekind (Id) in Type_Kind then
                  pragma Assert (Type_In_Container (Id));
                  Mark_Type_Entity (Id, In_Container => True);

               elsif Ekind (Id) in Subprogram_Kind then
                  Entities_In_Alfa.Include (Id);
               end if;
            end if;

            Next (Decl);
         end loop;
      end Declare_In_Container;

      Id         : constant Entity_Id := Defining_Entity (N);
      Vis_Decls  : constant List_Id :=
                     Visible_Declarations (Specification (N));
      Priv_Decls : constant List_Id :=
                     Private_Declarations (Specification (N));

   begin
      --  Do not analyze specs for instantiations of the formal containers.
      --  Only mark types in Alfa or not, and mark all subprograms in Alfa,
      --  but none should be scheduled for translation into Why3.

      if Is_Instantiation_Of_Formal_Container (N) then

         --  Explicitly add the package declaration to the entities to
         --  translate into Why3.

         if Current_Unit_Is_Main_Spec then
            Spec_Entities.Append (Id);

         elsif Current_Unit_Is_Main_Body then
            Body_Entities.Append (Id);
         end if;

         --  Mark types and subprograms from the formal container instantiation
         --  as in Alfa or not.

         Declare_In_Container (Vis_Decls);
         Declare_In_Container (Priv_Decls);

         return;
      end if;

      Push_Scope (Id);

      if Present (Vis_Decls) then
         Mark_List (Vis_Decls);
      end if;

      if Present (Priv_Decls) then
         Mark_List (Priv_Decls);
      end if;

      Pop_Scope (Id);
   end Mark_Package_Declaration;

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
                  Cur_Ent : constant Entity_Id := Current_Scope.Entity;

               begin
                  pragma Assert (Is_Subprogram (Cur_Ent)
                                  or else Ekind (Cur_Ent) = E_Package
                                  or else Ekind (Cur_Ent) = E_Package_Body);

                  --  Check that this is the first occurrence of this pragma
                  --  on the current entity.

                  if Formal_Proof_On.Contains (Cur_Ent) then
                     Error_Msg_N ("formal proof already forced for entity", N);
                     return;

                  elsif Formal_Proof_Off.Contains (Cur_Ent) then
                     Error_Msg_N
                       ("formal proof already disabled for entity", N);
                     return;
                  end if;

                  if Chars (Arg) = Name_Force then
                     if Formal_Proof_Currently_Forced then
                        Error_Msg_N ("?formal proof already forced", N);
                     end if;
                     Formal_Proof_On.Insert (Cur_Ent);
                  elsif Chars (Arg) = Name_Ignore then
                     if Formal_Proof_Currently_Disabled then
                        Error_Msg_N ("?formal proof already disabled", N);
                     end if;
                     Formal_Proof_Off.Insert (Cur_Ent);
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
                    and then (Has_Violations (Cur_Ent)
                               or else Has_Body_Violations (Cur_Ent))
                  then
                     Error_Msg_N
                       ("annotation is placed after violation of Alfa", N);
                     return;
                  end if;
               end;
            end if;

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

         --  Ignored pragmas, either because they are already taken into
         --  account (Precondition and Postcondition), or because they have no
         --  effect on verification (Export, Import, Preelaborate, Pure,
         --  Warnings).

         when Pragma_Export        |
              Pragma_Import        |
              Pragma_Precondition  |
              Pragma_Preelaborate  |
              Pragma_Postcondition |
              Pragma_Pure          |
              Pragma_Warnings      =>
            null;

         when others =>
            Mark_Violation ("pragma", N, NYI_Pragma);
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

      procedure Insert_All_And_Alfa (E : Entity_Id);

      -------------------------
      -- Insert_All_And_Alfa --
      -------------------------

      procedure Insert_All_And_Alfa (E : Entity_Id) is
      begin
         All_Entities.Insert (E);
         Entities_In_Alfa.Insert (E);
      end Insert_All_And_Alfa;

   begin
      for S in S_Types loop
         All_Entities.Insert (Standard_Entity (S));
         if Standard_Type_Is_In_Alfa (S) then
            Entities_In_Alfa.Insert (Standard_Entity (S));
            Entities_In_Alfa.Include (Etype (Standard_Entity (S)));
         end if;
      end loop;

      for S in S_ASCII_Names loop
         Insert_All_And_Alfa (Standard_Entity (S));
      end loop;

      Insert_All_And_Alfa (Standard_Void_Type);

      Insert_All_And_Alfa (Standard_False);
      Insert_All_And_Alfa (Standard_True);

      Insert_All_And_Alfa (Universal_Integer);
      Insert_All_And_Alfa (Universal_Real);
      Insert_All_And_Alfa (Universal_Fixed);

      Insert_All_And_Alfa (Standard_Integer_8);
      Insert_All_And_Alfa (Standard_Integer_16);
      Insert_All_And_Alfa (Standard_Integer_32);
      Insert_All_And_Alfa (Standard_Integer_64);
   end Mark_Standard_Package;

   --------------------------
   -- Mark_Subprogram_Body --
   --------------------------

   procedure Mark_Subprogram_Body (N : Node_Id) is
      Id  : constant Entity_Id := Unique_Defining_Entity (N);
      HSS : constant Node_Id   := Handled_Statement_Sequence (N);

   begin
      if not (Current_Unit_Is_Main_Spec or Current_Unit_Is_Main_Body) then
         return;
      end if;

      --  Content of formal containers is not to be proved

      if Location_In_Formal_Containers (Sloc (Id)) then
         return;
      end if;

      --  Do not analyze generic bodies

      if Ekind (Id) in Generic_Subprogram_Kind then
         return;
      end if;

      --  Inherit violations from spec to body

      if not In_Alfa (Id) then
         Inherit_Violations (Body_Violations, From => Id, To => Id);
      end if;

      --  Detect violations in the body itself

      Push_Scope (Id, Is_Body => True);
      Mark_List (Declarations (N));
      Mark (HSS);
      Pop_Scope (Id);

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

      -----------------------
      -- Local Subprograms --
      -----------------------

      procedure Mark_Function_Specification (N : Node_Id);
      --  Mark violations related to impure functions

      procedure Mark_Subprogram_Specification (N : Node_Id);
      --  Mark violations related to parameters, result and contract

      ---------------------------------
      -- Mark_Function_Specification --
      ---------------------------------

      procedure Mark_Function_Specification (N : Node_Id) is
         Id       : constant Entity_Id := Defining_Entity (N);
         Params   : constant List_Id   := Parameter_Specifications (N);
         Param    : Node_Id;
         Param_Id : Entity_Id;

      begin
         if Has_Global_Writes (Id) then
            Mark_Violation
              ("function with side-effects", Id, NIR_Impure_Function);
            return;
         end if;

         if Is_Non_Empty_List (Params) then
            Param := First (Params);
            while Present (Param) loop
               Param_Id := Defining_Identifier (Param);

               case Ekind (Param_Id) is
                  when E_Out_Parameter =>
                     Mark_Violation ("function with OUT parameter", Id,
                                     NIR_Impure_Function);
                     return;
                  when E_In_Out_Parameter =>
                     Mark_Violation ("function with IN OUT parameter", Id,
                                     NIR_Impure_Function);
                     return;
                  when others =>
                     null;
               end case;

               Next (Param);
            end loop;
         end if;
      end Mark_Function_Specification;

      -----------------------------------
      -- Mark_Subprogram_Specification --
      -----------------------------------

      procedure Mark_Subprogram_Specification (N : Node_Id) is
         Id         : constant Entity_Id := Defining_Entity (N);
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

               Push_Scope (Formal);

               if not In_Alfa (Etype (Formal)) then
                  Mark_Violation
                    ("type of formal", Param_Spec, From => Etype (Formal));
               end if;

               Pop_Scope (Formal);
               Next (Param_Spec);
            end loop;
         end if;

         --  If the result type of a subprogram is not in Alfa, then the
         --  subprogram is not in Alfa.

         if Nkind (N) = N_Function_Specification
           and then not In_Alfa (Etype (Id))
         then
            Mark_Violation
              ("return type", Result_Definition (N), From => Etype (Id));
         end if;
      end Mark_Subprogram_Specification;

      PPC  : Node_Id;
      CTC  : Node_Id;
      Req  : Node_Id;
      Ens  : Node_Id;
      Expr : Node_Id;
      Id   : constant Entity_Id := Defining_Entity (N);

   --  Start of Mark_Subprogram_Declaration

   begin
      --  Do not analyze generics

      if Ekind (Id) in Generic_Subprogram_Kind then
         return;
      end if;

      Push_Scope (Id);
      Mark_Subprogram_Specification (Specification (N));

      Push_Logic_Scope;

      PPC := Spec_PPC_List (Contract (Id));
      while Present (PPC) loop
         Expr := Get_Pragma_Arg (First (Pragma_Argument_Associations (PPC)));
         Mark (Expr);
         PPC := Next_Pragma (PPC);
      end loop;

      CTC := Spec_CTC_List (Contract (Id));
      while Present (CTC) loop
         if Pragma_Name (CTC) = Name_Contract_Case then
            Req := Get_Requires_From_CTC_Pragma (CTC);
            Ens := Get_Ensures_From_CTC_Pragma (CTC);
            if Present (Req) then
               Mark (Expression (Req));
            end if;
            if Present (Ens) then
               Mark (Expression (Ens));
            end if;
         end if;
         CTC := Next_Pragma (CTC);
      end loop;

      Pop_Logic_Scope;

      Pop_Scope (Id);
   end Mark_Subprogram_Declaration;

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

      if not In_Alfa (T) then
         Mark_Violation ("base type", N, From => T);
      end if;

      if Nkind (N) = N_Subtype_Indication then

         Cstr := Constraint (N);
         case Nkind (Cstr) is
            when N_Range_Constraint =>
               null;

            when N_Index_Or_Discriminant_Constraint =>

               if Is_Array_Type (T) then
                  Cstr := First (Constraints (Cstr));
                  while Present (Cstr) loop

                     case Nkind (Cstr) is
                     when N_Identifier | N_Expanded_Name =>
                        if not In_Alfa (Entity (Cstr)) then
                           Mark_Violation
                             ("index type", N, From => Entity (Cstr));
                        end if;

                     when N_Subtype_Indication =>
                        if not In_Alfa (Subtype_Mark (Cstr)) then
                           Mark_Violation
                             ("index type", N, From => Subtype_Mark (Cstr));
                        end if;

                     when N_Range =>
                        null;

                     when others =>
                        raise Program_Error;
                     end case;
                     Next (Cstr);
                  end loop;

               --  Note that a discriminant association that has no selector
               --  name list appears directly as an expression in the tree.

               else
                  null;
               end if;

            when N_Digits_Constraint =>
               null;

            when N_Delta_Constraint =>
               null;

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
         Mark_Violation
           ("type conversion not between scalar types", N, NYI_Conversion);
      end if;

      Mark (Expr);
   end Mark_Type_Conversion;

   ----------------------
   -- Mark_Type_Entity --
   ----------------------

   procedure Mark_Type_Entity (Id : Entity_Id; In_Container : Boolean) is

      procedure Mark_Violation
        (Msg : String;
         N   : Node_Id;
         V   : Alfa_Violations.Vkind);
      --  Local wrapper which does not issue violation when In_Container is
      --  True.

      procedure Mark_Violation
        (Msg  : String;
         N    : Node_Id;
         From : Entity_Id);
      --  Local wrapper which does not issue violation when In_Container is
      --  True.

      --------------------
      -- Mark_Violation --
      --------------------

      procedure Mark_Violation
        (Msg : String;
         N   : Node_Id;
         V   : Alfa_Violations.Vkind) is
      begin
         if not In_Container then
            Alfa.Definition.Mark_Violation (Msg, N, V);
         end if;
      end Mark_Violation;

      procedure Mark_Violation
        (Msg  : String;
         N    : Node_Id;
         From : Entity_Id) is
      begin
         if not In_Container then
            Alfa.Definition.Mark_Violation (Msg, N, From);
         end if;
      end Mark_Violation;

   begin
      --  Nothing to do if type was already marked

      if All_Entities.Contains (Id) then
         return;
      end if;

      --  Type declarations may refer to private types whose full view has not
      --  been declared yet. However, it is this full view which may define the
      --  type in Why3, if it happens to by in Alfa. Hence the need to define
      --  it now, so that it is available for the current type definition. So
      --  we start here with marking all needed types if not already marked.

      case Ekind (Id) is
         when Array_Kind =>
            declare
               Component_Typ : constant Node_Id := Component_Type (Id);
               Index         : Node_Id := First_Index (Id);
            begin
               if Present (Component_Typ) then
                  Mark_Type_Entity (Component_Typ, In_Container);
               end if;

               while Present (Index) loop
                  Mark_Type_Entity (Etype (Index), In_Container);
                  Next_Index (Index);
               end loop;
            end;

         --  Itypes may be generated by the frontend for component types.
         --  Mark them here, to avoid multiple definitions of the same type
         --  in multiple client packages.

         when E_Record_Type | E_Record_Subtype =>
            declare
               Field : Node_Id := First_Entity (Id);
            begin
               while Present (Field) loop
                  if Ekind (Field) in Object_Kind then
                     Mark_Type_Entity (Etype (Field), In_Container);
                  end if;
                  Next_Entity (Field);
               end loop;
            end;

         --  In the case of a package instantiation of a generic, the full view
         --  of a private type may not have a corresponding declaration. It is
         --  marked here.

         when Private_Kind =>
            Mark_Type_Entity (Underlying_Type (Id), In_Container);

         when others =>
            null;
      end case;

      --  Now mark the type itself

      Push_Scope (Id);

      --  Special case to accept subtypes and derived types of formal
      --  container types.

      if Location_In_Formal_Containers (Sloc (Etype (Id))) then
         goto Past_Violation_Detection;
      end if;

      if Is_Tagged_Type (Id) then
         Mark_Violation ("tagged type", Id, NYI_Tagged);
      end if;

      if Has_Invariants (Id) then
         Mark_Violation ("type invariant", Id, NYI_Invariant);
      end if;

      if Has_Predicates (Id) then
         Mark_Violation ("type predicate", Id, NYI_Predicate);
      end if;

      case Ekind (Id) is
         when Array_Kind =>
            declare
               Component_Typ : constant Node_Id := Component_Type (Id);
               Index         : Node_Id := First_Index (Id);

            begin
               --  Currently, array types of dimension 4 at most are supported

               if Number_Dimensions (Id) > 4 then
                  Mark_Violation ("array type", Id, NYI_Multi_Dim_Array);
               end if;

               --  Check that all index types are in Alfa

               while Present (Index) loop
                  if not In_Alfa (Etype (Index)) then
                     Mark_Violation
                       ("index type", Id, From => Etype (Index));
                  end if;
                  Next_Index (Index);
               end loop;

               --  Access definition for component type is not in Alfa

               if No (Component_Typ) then
                  Mark_Violation ("access type", Id, NIR_Access);
               end if;

               --  Check that component type is in Alfa

               if not In_Alfa (Component_Typ) then
                  Mark_Violation
                    ("component type", Id, From => Component_Typ);
               end if;
            end;

         --  Scalar types are always in Alfa

         when Integer_Kind | Real_Kind | Enumeration_Kind =>
            null;

         when E_Record_Type | E_Record_Subtype =>
            if Is_Interface (Id) then
               Mark_Violation ("interface", Id, NYI_Interface);

            else
               declare
                  Field : Node_Id := First_Component_Or_Discriminant (Id);
                  Typ   : Entity_Id;

               begin

                  while Present (Field) loop
                     Typ := Etype (Field);

                     if Ekind (Field) in Object_Kind
                       and then not In_Alfa (Typ)
                     then
                        Mark_Violation ("component type", Typ, From => Typ);
                     end if;

                     Next_Component_Or_Discriminant (Field);
                  end loop;
               end;
            end if;

         when E_Class_Wide_Type    |
              E_Class_Wide_Subtype =>
            Mark_Violation ("type definition", Id, NYI_Class_Wide);

         when Access_Kind =>
            Mark_Violation ("access type", Id, NIR_Access);

         when Concurrent_Kind =>
            Mark_Violation ("tasking", Id, NIR_Tasking);

         when Private_Kind =>

            --  Store correspondance between full and partial view, so that
            --  generation of Why can use this information.

            if Present (Full_View (Id)) then
               Add_Full_And_Partial_View (Full_View (Id), Id);
            end if;

            --  Private types that are not a record type or subtype are in Alfa

            if Ekind_In (Id, E_Record_Type_With_Private,
                         E_Record_Subtype_With_Private)
            then
               Mark_Violation ("type definition", Id, NYI_Tagged);
            end if;

         when others =>
            raise Program_Error;
      end case;

      << Past_Violation_Detection >>

      --  If the type is in a formal container package instance, insert it in
      --  the set of entities already treated before calling Pop_Scope, so that
      --  it is only marked in Alfa if necessary, but it is not marked for
      --  translation into Why3.

      if In_Container then
         All_Entities.Insert (Id);
      end if;

      Pop_Scope (Id);
   end Mark_Type_Entity;

   -------------------
   -- Mark_Unary_Op --
   -------------------

   procedure Mark_Unary_Op (N : Node_Id) is
      T : constant Entity_Id := Etype (Right_Opnd (N));

   begin
      case N_Unary_Op'(Nkind (N)) is
         when N_Op_Not =>
            if Is_Array_Type (T) then
               Mark_Violation
                 ("not operator on array type", N, NYI_Arith_Operation);
            end if;

         when N_Op_Abs | N_Op_Plus | N_Op_Minus =>
            null;
      end case;

      Mark (Right_Opnd (N));
   end Mark_Unary_Op;

   ------------------------------------
   -- Mark_Violations_For_All_Scopes --
   ------------------------------------

   procedure Mark_Violations_For_All_Scopes is

      generic
         with procedure Mark_Body_Violations (E : Entity_Id) is <>;
         with procedure Mark_Spec_Violations (E : Entity_Id) is <>;
      procedure Mark_Violations (Scop : Scope_Record);
      --  Attach violations to the entity of scope Scop

      ---------------------
      -- Mark_Violations --
      ---------------------

      procedure Mark_Violations (Scop : Scope_Record) is
         Ent : Entity_Id;

      begin
         if Scop.Is_Logic then
            return;
         end if;

         Ent := Scop.Entity;
         case Ekind (Ent) is

            --  Detect violation in initialization of package-level object

         when Object_Kind | Named_Kind =>
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

            --  Detect violation in subprogram declarations and subprogram
            --  bodies

            --  If the non-Alfa construct is in a precondition or
            --  postcondition, then mark the subprogram as not in Alfa, because
            --  neither the subprogram nor its callers can be proved formally.

            --  If the non-Alfa construct is in a regular piece of code inside
            --  the body of the subprogram, then mark the subprogram body as
            --  not in Alfa, because the subprogram cannot be proved formally,
            --  but its callers could.

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

      procedure Mark_Scope is new Mark_Violations;
      procedure Iterate_Scope is new Iterate (Mark_Scope);
   begin
      Iterate_Scope;
   end Mark_Violations_For_All_Scopes;

   ----------------------------------
   -- Most_Underlying_Type_In_Alfa --
   ----------------------------------

   procedure Mark_Most_Underlying_Type_In_Alfa (Id : Entity_Id; N : Node_Id) is
      Typ : constant Entity_Id := Most_Underlying_Type (Id);
   begin
      if not In_Alfa (Typ) then
         Mark_Violation ("type", N, From => Typ);
      end if;
   end Mark_Most_Underlying_Type_In_Alfa;

   -----------------
   -- Scope_Stack --
   -----------------

   package body Scope_Stack is

      First_Scope_Index : constant := 0;

      package Scope_Table is
        new Table.Table
          (Table_Component_Type => Scope_Record,
           Table_Index_Type     => Int,
           Table_Low_Bound      => First_Scope_Index,
           Table_Initial        => Alloc.Scope_Stack_Initial,
           Table_Increment      => Alloc.Scope_Stack_Increment,
           Table_Name           => "Alfa.Definition.Scope_Stack");

      -------------------
      -- Current_Scope --
      -------------------

      function Current_Scope return Scope_Record is
        (Scope_Table.Table (Scope_Table.Last));

      -------------------------------------
      -- Formal_Proof_Currently_Disabled --
      -------------------------------------

      function Formal_Proof_Currently_Disabled return Boolean is
      begin
         for Idx in reverse Scope_Table.First .. Scope_Table.Last loop
            declare
               E : constant Entity_Id := Scope_Table.Table (Idx).Entity;
            begin
               if Formal_Proof_Off.Contains (E) then
                  return True;
               elsif Formal_Proof_On.Contains (E) then
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
         for Idx in reverse Scope_Table.First .. Scope_Table.Last loop
            if not Scope_Table.Table (Idx).Is_Logic then
               declare
                  E : constant Entity_Id :=
                    Scope_Table.Table (Idx).Entity;
               begin
                  if Formal_Proof_On.Contains (E) then
                     return True;
                  elsif Formal_Proof_Off.Contains (E) then
                     return False;
                  end if;
               end;
            end if;
         end loop;
         return False;
      end Formal_Proof_Currently_Forced;

      --------------------
      -- In_Logic_Scope --
      --------------------

      function In_Logic_Scope return Boolean is
         Cur_Scop : Scope_Record renames Scope_Table.Table (Scope_Table.Last);
      begin
         return Cur_Scop.Is_Logic;
      end In_Logic_Scope;

      -------------
      -- Iterate --
      -------------

      procedure Iterate is
      begin
         for Scope in First_Scope_Index .. Scope_Table.Last loop
            Iterator (Scope_Table.Table (Scope));
         end loop;
      end Iterate;

      ---------------------
      -- Pop_Logic_Scope --
      ---------------------

      procedure Pop_Logic_Scope is
         Cur_Scop : Scope_Record renames Scope_Table.Table (Scope_Table.Last);
      begin
         pragma Assert (Cur_Scop.Is_Logic);
         Scope_Table.Decrement_Last;
      end Pop_Logic_Scope;

      ---------------
      -- Pop_Scope --
      ---------------

      procedure Pop_Scope (E : Entity_Id) is
         Cur_Scope : Scope_Record renames Scope_Table.Table (Scope_Table.Last);
         Body_N    : Node_Id;
         Insert_E  : Entity_Id;
      begin
         pragma Assert (Cur_Scope.Entity = E);
         Scope_Table.Decrement_Last;

         --  For the special case of an expression function, the frontend
         --  generates a distinct body if not already in source code. Use as
         --  entity for the body the distinct E_Subprogram_Body entity. This
         --  allows a separate definition of theories in Why3 for declaring
         --  the logic function and its axiom. This is necessary so that they
         --  are defined with the proper visibility over previously defined
         --  entities.

         Insert_E := E;

         if Cur_Scope.Is_Body
           and then Ekind (E) = E_Function
           and then Present (Get_Expression_Function (E))
         then
            Body_N   := Alfa.Util.Get_Subprogram_Body (E);
            Insert_E := Defining_Entity (Body_N);
            pragma Assert (Ekind (Insert_E) = E_Subprogram_Body);
         end if;

         --  Now insert the entity Insert_E if not already done

         if not All_Entities.Contains (Insert_E) then
            All_Entities.Insert (Insert_E);

            --  Package scopes do not lead to a translation to Why3

            if Ekind (Insert_E) = E_Package then
               null;

            elsif Current_Unit_Is_Main_Spec then
               Spec_Entities.Append (Insert_E);

            elsif Current_Unit_Is_Main_Body then
               Body_Entities.Append (Insert_E);
            end if;
         end if;

         --  Finally mark the entity (body) in Alfa if appropriate

         if Cur_Scope.Is_Body then
            if not Has_Body_Violations (E) then
               Bodies_In_Alfa.Include (E);
            end if;
         else
            if not Has_Violations (E) then
               Entities_In_Alfa.Include (E);
            end if;
         end if;
      end Pop_Scope;

      ----------------------
      -- Push_Logic_Scope --
      ----------------------

      procedure Push_Logic_Scope is
      begin
         Scope_Table.Increment_Last;
         Scope_Table.Table (Scope_Table.Last) :=
           Scope_Record'(Is_Logic => True);
      end Push_Logic_Scope;

      ----------------
      -- Push_Scope --
      ----------------

      procedure Push_Scope (E : Entity_Id; Is_Body : Boolean := False) is
      begin
         Scope_Table.Increment_Last;
         Scope_Table.Table (Scope_Table.Last) :=
           Scope_Record'(Entity     => E,
                         Is_Body    => Is_Body,
                         Is_Logic   => False);
      end Push_Scope;

   end Scope_Stack;

end Alfa.Definition;
