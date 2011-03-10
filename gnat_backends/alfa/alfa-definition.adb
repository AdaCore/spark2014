------------------------------------------------------------------------------
--                                                                          --
--                         GNAT BACK-END COMPONENTS                         --
--                                                                          --
--                       A L F A . D E F I N I T I O N                      --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--             Copyright (C) 2011, Free Software Foundation, Inc.           --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License --
-- for  more details.  You should have  received  a copy of the GNU General --
-- Public License  distributed with GNAT; see file COPYING3.  If not, go to --
-- http://www.gnu.org/licenses for a complete copy of the license.          --
--                                                                          --
-- GNAT was originally developed  by the GNAT team at  New York University. --
-- Extensive contributions were provided by Ada Core Technologies Inc.      --
--                                                                          --
------------------------------------------------------------------------------

with Alloc;       use Alloc;
with Atree;       use Atree;
with Einfo;       use Einfo;
with Errout;      use Errout;
with Namet;       use Namet;
with Nlists;      use Nlists;
with Snames;      use Snames;
with Sem_Eval;    use Sem_Eval;
with Sem_Util;    use Sem_Util;
with Sinfo;       use Sinfo;
with Stand;       use Stand;
with Table;

with ALFA.Common; use ALFA.Common;

package body ALFA.Definition is

   ---------------------
   -- Local Constants --
   ---------------------

   --  Standard types which are in ALFA are associated set to True

   Standard_Type_Is_In_ALFA : constant array (S_Types) of Boolean :=
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

      S_Character           => False,  --  TO DO: set to True
      S_Wide_Character      => False,
      S_Wide_Wide_Character => False,

      S_String              => False,  --  TO DO: set to True
      S_Wide_String         => False,
      S_Wide_Wide_String    => False,

      S_Duration            => False);

   -------------------------
   -- Pragma Formal_Proof --
   -------------------------

   Formal_Proof_On  : Id_Set.Set;
   Formal_Proof_Off : Id_Set.Set;

   function Formal_Proof_Currently_Forced return Boolean;
   --  Determine the most top-level scope to have formal proof forced or
   --  disabled, and return True if formal proof is forced. Return False in all
   --  other cases. This is useful to notify the user about ALFA violations in
   --  a scope where formal proof is forced.

   ----------------
   -- ALFA Marks --
   ----------------

   Standard_In_ALFA : Id_Set.Set;
   --  Entities from package Standard which are in ALFA

   type Violations is array (Violation_Kind) of Id_Set.Set;

   Spec_Violations : Violations;
   --  Sets of entities which violate ALFA restrictions, per violation kind

   Body_Violations : Violations;
   --  Sets of subprogram entities whose body violate ALFA restrictions, per
   --  violation kind.

   function Complete_Error_Msg (Msg : String; Implem : Boolean) return String;

   procedure Inherit_Violations (A : in out Violations; To, From : Entity_Id);

   -----------------
   -- Scope Stack --
   -----------------

   type Scope_Record is record
      Entity  : Entity_Id;
      Is_Body : Boolean;
   end record;

   package Scope_Stack is new Table.Table (
     Table_Component_Type => Scope_Record,
     Table_Index_Type     => Int,
     Table_Low_Bound      => 0,
     Table_Initial        => Alloc.Scope_Stack_Initial,
     Table_Increment      => Alloc.Scope_Stack_Increment,
     Table_Name           => "ALFA.Definition.Scope_Stack");

   function Current_Scope return Scope_Record;
   --  Return the top-most scope that is not a loop

   function Has_Loop_In_Inner_Open_Scopes (S : Entity_Id) return Boolean;
   --  S is the entity of an open scope. This function determines if there is
   --  an inner scope of S which is a loop (i.e. it appears somewhere in the
   --  scope stack after S).

   procedure Pop_Scope;
   --  Remove the top scope in the stack

   procedure Push_Scope (E : Entity_Id; Is_Body : Boolean := False);
   --  Set entity S as the top scope in the stack

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Mark (N : Node_Id);
   --  Generic procedure for marking code as in ALFA / not in ALFA

   procedure Mark_List (L : List_Id);
   --  Call Mark on all nodes in list L

   procedure Mark_Non_ALFA_Declaration
     (Msg : String;
      N   : Node_Id;
      V   : Violation_Kind := V_Other);
   --  Mark the declaration N as not being in ALFA, as well as the enclosing
   --  subprogram if any.

   procedure Mark_Non_ALFA_Declaration
     (Msg  : String;
      N    : Node_Id;
      From : Entity_Id);

   procedure Mark_In_Non_ALFA_Subprogram
     (Msg : String;
      N   : Node_Id;
      V   : Violation_Kind := V_Other);
   --  Mark the current subprogram containing node N (if any) as not being in
   --  ALFA. If the corresponding scope is marked as spec-only, then mark the
   --  subprogram specification as not in ALFA. Otherwise, mark the subprogram
   --  body as not in ALFA.
   --
   --  Indeed, this procedure may be called during the analysis of a
   --  precondition or postcondition, or during the analysis of a subprogram's
   --  body. In the first case, the specification of the current subprogram
   --  must be marked as not being in ALFA, as the contract is considered to be
   --  part of the specification, so that calls to this subprogram are not in
   --  ALFA. In the second case, mark the body as not being in ALFA, which does
   --  not prevent the subprogram's specification, and calls to the subprogram,
   --  from being in ALFA.
   --
   --  If the subprogram being marked as not in ALFA is annotated with
   --  Formal_Proof On, then an error is issued with message Msg on node N.

   procedure Mark_In_Non_ALFA_Subprogram
     (Msg  : String;
      N    : Node_Id;
      From : Entity_Id);

   --  Special treatment for marking some kinds of nodes

   procedure Mark_Attribute_Reference         (N : Node_Id);
   procedure Mark_Binary_And_Short_Circuit_Op (N : Node_Id);
   procedure Mark_Call                        (N : Node_Id);
   procedure Mark_Conditional_Expression      (N : Node_Id);
   procedure Mark_Exit_Statement              (N : Node_Id);
   procedure Mark_Full_Type_Declaration       (N : Node_Id);
   procedure Mark_Handled_Statements          (N : Node_Id);
   procedure Mark_Identifier_Or_Expanded_Name (N : Node_Id);
   procedure Mark_Iteration_Scheme            (N : Node_Id);
   procedure Mark_Loop_Statement              (N : Node_Id);
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
   procedure Mark_Subtype_Indication_In_Decl  (N : Node_Id);
   procedure Mark_Type_Conversion             (N : Node_Id);

   ---------------------
   -- Body_Is_In_ALFA --
   ---------------------

   function Body_Is_In_ALFA (Id : Entity_Id) return Boolean is
   begin
      return (for all S of Body_Violations => not S.Contains (Id));
   end Body_Is_In_ALFA;

   ------------------------
   -- Complete_Error_Msg --
   ------------------------

   function Complete_Error_Msg (Msg : String; Implem : Boolean) return String
   is
   begin
      if Implem then
         return Msg & " is in ALFA but not yet supported";
      else
         return Msg & " is not in ALFA";
      end if;
   end Complete_Error_Msg;

   -------------------
   -- Current_Scope --
   -------------------

   function Current_Scope return Scope_Record is
      Idx : Int := Scope_Stack.Last;

   begin
      while Idx /= -1
        and then Ekind (Scope_Stack.Table (Idx).Entity) = E_Loop
      loop
         Idx := Idx - 1;
      end loop;

      pragma Assert (Idx /= -1);

      return Scope_Stack.Table (Idx);
   end Current_Scope;

   -----------------------------------
   -- Formal_Proof_Currently_Forced --
   -----------------------------------

   function Formal_Proof_Currently_Forced return Boolean is
   begin
      for Idx in reverse Scope_Stack.First .. Scope_Stack.Last loop
         declare
            E : constant Entity_Id := Scope_Stack.Table (Idx).Entity;
         begin
            if Formal_Proof_On.Contains (E) then
               return True;
            elsif Formal_Proof_Off.Contains (E) then
               return False;
            end if;
         end;
      end loop;
      return False;
   end Formal_Proof_Currently_Forced;

   -----------------------------------
   -- Has_Loop_In_Inner_Open_Scopes --
   -----------------------------------

   function Has_Loop_In_Inner_Open_Scopes (S : Entity_Id) return Boolean is
   begin
      for J in reverse 0 .. Scope_Stack.Last loop

         --  S was reached without seing a loop scope first

         if Scope_Stack.Table (J).Entity = S then
            return False;

         --  S was not yet reached, so it contains at least one inner loop

         elsif Ekind (Scope_Stack.Table (J).Entity) = E_Loop then
            return True;
         end if;
      end loop;

      raise Program_Error;    --  unreachable
   end Has_Loop_In_Inner_Open_Scopes;

   ------------------------
   -- Inherit_Violations --
   ------------------------

   procedure Inherit_Violations (A : in out Violations; To, From : Entity_Id)
   is
   begin
      if Scope (From) = Standard_Standard then
         A (V_Other).Include (To);
      else
         pragma Assert (for some S of Spec_Violations => S.Contains (From));

         for V in Violation_Kind loop
            if Spec_Violations (V).Contains (From) then
               A (V).Include (To);
            end if;
         end loop;
      end if;
   end Inherit_Violations;

   ----------------
   -- Is_In_ALFA --
   ----------------

   function Is_In_ALFA (Id : Entity_Id) return Boolean is
   begin
      if Scope (Id) = Standard_Standard
        and then not (Is_Subprogram (Id)
                       or else Ekind (Id) = E_Package)
      then
         return Standard_In_ALFA.Contains (Id);
      else
         return (for all S of Spec_Violations => not S.Contains (Id));
      end if;
   end Is_In_ALFA;

   ----------
   -- Mark --
   ----------

   procedure Mark (N : Node_Id) is
   begin
      case Nkind (N) is
         when N_Abstract_Subprogram_Declaration =>  --  TO DO
            Mark_In_Non_ALFA_Subprogram ("abstract subprogram", N);

         when N_Aggregate =>  --  TO DO
            Mark_In_Non_ALFA_Subprogram ("aggregate", N, V_Implem);

         when N_Allocator =>
            Mark_In_Non_ALFA_Subprogram ("allocator", N);

         when N_Assignment_Statement =>
            Mark (Name (N));
            Mark (Expression (N));

         when N_At_Clause =>  -- TO DO
            Mark_In_Non_ALFA_Subprogram ("at clause", N);

         when N_Attribute_Reference =>
            Mark_Attribute_Reference (N);

         when N_Attribute_Definition_Clause   =>
            Mark_In_Non_ALFA_Subprogram
              ("attribute definition clause", N);

         when N_Binary_Op =>
            Mark_Binary_And_Short_Circuit_Op (N);

         when N_Block_Statement =>
            Mark_In_Non_ALFA_Subprogram
              ("block statement", N, V_Block_Statement);

            Mark_List (Declarations (N));
            Mark (Handled_Statement_Sequence (N));

         when N_Case_Expression =>
            Mark_In_Non_ALFA_Subprogram ("case expression", N, V_Implem);

         when N_Case_Statement =>
            Mark (Expression (N));

            declare
               Alt : Node_Id;
            begin
               Alt := First (Alternatives (N));
               while Present (Alt) loop
                  Mark_List (Statements (Alt));
                  Next (Alt);
               end loop;
            end;

         when N_Character_Literal =>
            null;

         when N_Code_Statement =>
            Mark_In_Non_ALFA_Subprogram ("code statement", N);

         when N_Compilation_Unit =>
            Mark (N);  --  useful???

         when N_Component_Declaration =>
            raise Program_Error;  --  TO DO when treating records

         when N_Conditional_Expression =>
            Mark_Conditional_Expression (N);

         when N_Enumeration_Representation_Clause =>
            Mark_In_Non_ALFA_Subprogram
              ("enumeration representation clause", N);

         when N_Exception_Declaration          |
              N_Exception_Renaming_Declaration =>
            Mark_Non_ALFA_Declaration ("exception", N);

         when N_Exit_Statement =>
            Mark_Exit_Statement (N);

         when N_Expanded_Name =>
            Mark_Identifier_Or_Expanded_Name (N);

         when N_Explicit_Dereference =>
            Mark_In_Non_ALFA_Subprogram ("explicit dereference", N);

         when N_Expression_Function =>  --  TO DO
            Mark_In_Non_ALFA_Subprogram ("expression function", N, V_Implem);

         when N_Expression_With_Actions =>  --  TO DO

            --  ??? Currently ignore these.
            null;

         when N_Extended_Return_Statement =>
            Mark_In_Non_ALFA_Subprogram ("extended RETURN", N);

         when N_Extension_Aggregate =>
            Mark_In_Non_ALFA_Subprogram ("extension aggregate", N, V_Implem);

         when N_Formal_Object_Declaration |
              N_Formal_Package_Declaration |
              N_Formal_Subprogram_Declaration |
              N_Formal_Type_Declaration =>
            Mark_Non_ALFA_Declaration ("formal generic parameter", N);

         when N_Free_Statement =>
            Mark_In_Non_ALFA_Subprogram ("free statement", N);

         when N_Freeze_Entity =>
            if Present (Actions (N)) then
               Mark_List (Actions (N));
            end if;

         when N_Full_Type_Declaration =>
            Mark_Full_Type_Declaration (N);

         when N_Function_Call =>
            Mark_Call (N);

         when N_Function_Instantiation =>
            Mark_In_Non_ALFA_Subprogram ("function instantiation", N);

         when N_Generic_Function_Renaming_Declaration |
              N_Generic_Package_Declaration |
              N_Generic_Package_Renaming_Declaration |
              N_Generic_Procedure_Renaming_Declaration |
              N_Generic_Subprogram_Declaration =>
            Mark_In_Non_ALFA_Subprogram ("generic declaration", N);

         when N_Goto_Statement =>
            Mark_In_Non_ALFA_Subprogram ("goto statement", N);

         when N_Handled_Sequence_Of_Statements =>
            Mark_Handled_Statements (N);

         when N_Identifier =>
            Mark_Identifier_Or_Expanded_Name (N);

         when N_If_Statement =>
            Mark (Condition (N));

            --  ??? Currently recognize specially the code generated for a
            --  pragma assert, to avoid marking the call to
            --  Raise_Assert_Failure as not in ALFA. To be removed asap.

            if Nkind (Original_Node (N)) = N_Pragma and then
              (Get_Name_String
                 (Chars (Pragma_Identifier (Original_Node (N)))) = "assert"
               or else
                 Get_Name_String
                   (Chars (Pragma_Identifier (Original_Node (N)))) = "check")
            then
               return;
            end if;

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
                        raise Program_Error;  --  TO DO
                     end if;

                     Next (Part);
                  end loop;
               end;
            end if;

            if Present (Else_Statements (N)) then
               Mark_List (Else_Statements (N));
            end if;

         when N_Implicit_Label_Declaration =>
            null;

         when N_In =>
            null;

         when N_Incomplete_Type_Declaration =>
            null;

         when N_Indexed_Component =>
            Mark (Prefix (N));
            Mark_List (Expressions (N));

         when N_Integer_Literal =>
            null;

         when N_Iterator_Specification =>
            Mark_In_Non_ALFA_Subprogram ("iterator specification", N);

         when N_Itype_Reference =>
            null;

         when N_Label =>
            null;

         when N_Loop_Statement =>
            Mark_Loop_Statement (N);

         when N_Not_In =>
            null;

         when N_Null =>
            Mark_In_Non_ALFA_Subprogram ("null", N);

         when N_Null_Statement =>
            null;

         when N_Number_Declaration =>
            null;

         when N_Object_Declaration =>
            Mark_Object_Declaration (N);

         when N_Object_Renaming_Declaration  =>
            Mark_Object_Renaming_Declaration (N);

         when N_Operator_Symbol =>
            null;

         when N_Unary_Op =>
            Mark (Right_Opnd (N));

         when N_Others_Choice =>
            null;

         when N_Package_Body =>
            Mark_Package_Body (N);

         when N_Package_Body_Stub =>
            null;

         when N_Package_Declaration =>
            Mark_Package_Declaration (N);

         when N_Package_Instantiation =>
            Mark_In_Non_ALFA_Subprogram ("package instantiation", N);

         when N_Package_Renaming_Declaration =>
            null;

         when N_Package_Specification =>
            Mark_Package_Specification (N);

         when N_Parameter_Association =>
            Mark (Explicit_Actual_Parameter (N));

         when N_Pragma =>
            Mark_Pragma (N);

         when N_Private_Extension_Declaration =>
            null;

         when N_Private_Type_Declaration =>
            null;

         when N_Procedure_Call_Statement =>

            --  ??? Currently recognize specially the code generated for a
            --  postcondition, to avoid marking this call as not in ALFA. To be
            --  removed asap.

            if Is_Entity_Name (Name (N))
              and then Is_Postcondition_Proc (Entity (Name (N)))
            then
               return;
            end if;

            Mark_Call (N);

         when N_Procedure_Instantiation =>
            Mark_In_Non_ALFA_Subprogram ("procedure instantiation", N);

         when N_Qualified_Expression =>
            Mark_In_Non_ALFA_Subprogram ("qualified expression", N, V_Implem);

         when N_Quantified_Expression =>
            Mark_In_Non_ALFA_Subprogram ("quantified expression", N, V_Implem);

         when N_Raise_Statement =>
            Mark_In_Non_ALFA_Subprogram ("raise statement", N);

         when N_Raise_xxx_Error =>

            --  ??? Currently consider specially these as checks inserted by
            --  by the compiler. To be removed asap.

            null;

         when N_Range =>
            Mark (Low_Bound (N));
            Mark (High_Bound (N));

         when N_Range_Constraint =>
            raise Program_Error;  --  TO DO???

         when N_Real_Literal =>
            null;

         when N_Record_Representation_Clause =>
            Mark_In_Non_ALFA_Subprogram
              ("record representation clause", N);

         when N_Reference =>
            raise Program_Error;  --  TO DO???

         when N_Short_Circuit =>
            Mark_Binary_And_Short_Circuit_Op (N);

         when N_Simple_Return_Statement =>
            Mark_Simple_Return_Statement (N);

         when N_Selected_Component =>  --  TO DO when treating records
            Mark_In_Non_ALFA_Subprogram
              ("selected component", N, V_Implem);

         when N_Slice =>
            Mark_In_Non_ALFA_Subprogram ("slice", N, V_Slice);

         when N_String_Literal =>
            null;

         when N_Subprogram_Body =>
            Mark_Subprogram_Body (N);

         when N_Subprogram_Body_Stub =>
            null;

         when N_Subprogram_Declaration =>
            Mark_Subprogram_Declaration (N);

         when N_Subprogram_Info =>
            null;

         when N_Subprogram_Renaming_Declaration =>
            null;

         when N_Subtype_Declaration =>
            Mark_Subtype_Indication_In_Decl (N);

         when N_Subtype_Indication =>
            raise Program_Error;  --  TO DO???

         when N_Subunit =>
            raise Program_Error;  --  TO DO???

         when N_Type_Conversion =>
            Mark_Type_Conversion (N);

         when N_Unchecked_Expression =>
            Mark_In_Non_ALFA_Subprogram ("unchecked expression", N);

         when N_Unchecked_Type_Conversion =>
            Mark_In_Non_ALFA_Subprogram ("unchecked type conversion", N);

         when N_Use_Package_Clause =>
            null;

         when N_Use_Type_Clause =>
            null;

         when N_Validate_Unchecked_Conversion =>
            Mark_In_Non_ALFA_Subprogram ("unchecked conversion", N);

         when N_Variant_Part =>
            Mark_In_Non_ALFA_Subprogram ("variant part", N, V_Discr);

         when N_With_Clause =>
            null;

         when others =>
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
         when Attribute_Result | Attribute_Old =>
            null;
         when others =>
            Mark_In_Non_ALFA_Subprogram ("attribute", N, V_Implem);
      end case;

      Mark (P);
      if Present (Exprs) then
         Mark_List (Exprs);
      end if;
   end Mark_Attribute_Reference;

   --------------------------------------
   -- Mark_Binary_And_Short_Circuit_Op --
   --------------------------------------

   procedure Mark_Binary_And_Short_Circuit_Op (N : Node_Id) is
      Left_T : constant Entity_Id := Etype (Left_Opnd (N));

   begin
      case Nkind (N) is
         when N_Op_Concat =>
            Mark_In_Non_ALFA_Subprogram ("concatenation", N, V_Implem);

         when N_Op_Lt | N_Op_Le | N_Op_Gt | N_Op_Ge =>
            if Is_Boolean_Type (Left_T) then
               Mark_In_Non_ALFA_Subprogram
                 ("ordering operator on boolean type", N);

            elsif Is_Array_Type (Left_T) then
               Mark_In_Non_ALFA_Subprogram
                 ("ordering operator on array type", N);
            end if;

         when N_Op_Eq | N_Op_Ne =>
            if Is_Array_Type (Left_T) then
               Mark_In_Non_ALFA_Subprogram
                 ("equality operator on array type", N);
            end if;

         when N_Op_And | N_Op_Or | N_Op_Xor =>
            if Is_Array_Type (Left_T)
              and then Nkind (N) in N_Binary_Op
            then
               Mark_In_Non_ALFA_Subprogram
                 ("binary operator on array type", N);
            end if;

         when others =>
            null;
      end case;

      Mark (Left_Opnd (N));
      Mark (Right_Opnd (N));
   end Mark_Binary_And_Short_Circuit_Op;

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
      --  operation or the subprogram called is not in ALFA, then the call is
      --  not in ALFA.

      if not Is_Entity_Name (Nam) then
         Mark_In_Non_ALFA_Subprogram ("call", N);
      elsif not Is_In_ALFA (Entity (Nam)) then
         Mark_In_Non_ALFA_Subprogram
           ("subprogram called", N, From => Entity (Nam));
      end if;
   end Mark_Call;

   ---------------------------
   -- Mark_Compilation_Unit --
   ---------------------------

   procedure Mark_Compilation_Unit (N : Node_Id) is
   begin
      --  Separately mark declarations from Standard as in ALFA or not

      if Defining_Entity (N) /= Standard_Standard then
         Push_Scope (Standard_Standard);
         Mark (N);
         Pop_Scope;
      end if;
   end Mark_Compilation_Unit;

   ---------------------------------
   -- Mark_Conditional_Expression --
   ---------------------------------

   procedure Mark_Conditional_Expression (N : Node_Id) is
      Condition : constant Node_Id := First (Expressions (N));
      Then_Expr : constant Node_Id := Next (Condition);
      Else_Expr : Node_Id;

   begin
      Else_Expr := Next (Then_Expr);

      --  In ALFA, boolean conditional expressions are allowed:
      --    * if they have no ELSE part, in which case the expression is
      --      equivalent to
      --
      --        NOT Condition OR ELSE Then_Expr
      --
      --    * in pre- and postconditions, where the Condition cannot have side-
      --      effects (in ALFA) and thus the expression is equivalent to
      --
      --        (Condition AND THEN Then_Expr)
      --          and (NOT Condition AND THEN Then_Expr)

      if Present (Else_Expr)
        and then Current_Scope.Is_Body
      then
         Mark_In_Non_ALFA_Subprogram ("form of conditional expression", N);
      end if;

      if Root_Type (Etype (N)) /= Standard_Boolean then
         Mark_In_Non_ALFA_Subprogram
           ("non-boolean conditional expression", N);
      end if;

      Mark (Condition);
      Mark (Then_Expr);

      if Present (Else_Expr) then
         Mark (Else_Expr);
      end if;
   end Mark_Conditional_Expression;

   -------------------------
   -- Mark_Exit_Statement --
   -------------------------

   procedure Mark_Exit_Statement (N : Node_Id) is
      Target : constant Node_Id := Name (N);
      Cond   : constant Node_Id := Condition (N);
      U_Name : Entity_Id;

   begin
      if Present (Target) then
         U_Name := Entity (Target);

         if Has_Loop_In_Inner_Open_Scopes (U_Name) then
            Mark_In_Non_ALFA_Subprogram
              ("exit label naming some outter loop", N);
         end if;
      end if;

      if Present (Cond) then
         if Nkind (Parent (N)) /= N_Loop_Statement then
            Mark_In_Non_ALFA_Subprogram
              ("exit with when clause not directly in loop", N);
         end if;

      else
         if Nkind (Parent (N)) /= N_If_Statement then
            if Nkind (Parent (N)) = N_Elsif_Part then
               Mark_In_Non_ALFA_Subprogram
                 ("exit in IF with ELSIF", N);
            else
               Mark_In_Non_ALFA_Subprogram
                 ("exit not directly in IF", N);
            end if;

         elsif Nkind (Parent (Parent (N))) /= N_Loop_Statement then
            Mark_In_Non_ALFA_Subprogram
              ("exit not in IF directly in loop", N);

         --  First test the presence of ELSE, so that an exit in an ELSE leads
         --  to an error mentioning the ELSE.

         elsif Present (Else_Statements (Parent (N))) then
            Mark_In_Non_ALFA_Subprogram
              ("exit in IF with ELSE", N);

         --  An exit in an ELSIF does not reach here, as it would have been
         --  detected in the case (Nkind (Parent (N)) /= N_If_Statement).

         elsif Present (Elsif_Parts (Parent (N))) then
            Mark_In_Non_ALFA_Subprogram
              ("exit in IF with ELSIF", N);
         end if;
      end if;
   end Mark_Exit_Statement;

   --------------------------------
   -- Mark_Full_Type_Declaration --
   --------------------------------

   procedure Mark_Full_Type_Declaration (N : Node_Id) is
      Id  : constant Entity_Id := Defining_Identifier (N);
      Def : constant Node_Id   := Type_Definition (N);

   begin
      case Nkind (Def) is
         when N_Array_Type_Definition =>
            declare
               Component_Def : constant Node_Id := Component_Definition (Def);
               Component_Typ : constant Node_Id :=
                                 Subtype_Indication (Component_Def);
               Index         : Node_Id;

            begin
               if Nkind (Def) = N_Constrained_Array_Definition then
                  Index := First (Discrete_Subtype_Definitions (Def));
               else
                  Index := First (Subtype_Marks (Def));
               end if;

               --  Check that all index types are in ALFA

               while Present (Index) loop
                  if not Is_In_ALFA (Etype (Index)) then
                     Mark_Non_ALFA_Declaration
                       ("index type", N, From => Etype (Index));
                  end if;
                  Next_Index (Index);
               end loop;

               --  Access definition for component type is not in ALFA

               if No (Component_Typ) then
                  Mark_Non_ALFA_Declaration ("access type", N);
               end if;

               --  Check that component type is in ALFA

               if not Is_In_ALFA (Etype (Component_Typ)) then
                  Mark_Non_ALFA_Declaration
                    ("component type", N, From => Etype (Component_Typ));
               end if;

               --  Check that array bounds are static

               if Nkind (Def) = N_Constrained_Array_Definition
                 and then not Has_Static_Array_Bounds (Id)
               then
                  Mark_Non_ALFA_Declaration
                    ("array type with non-static bounds", N);
               end if;
            end;

         when N_Enumeration_Type_Definition =>
            --  Enumeration type is in ALFA only if it is not a character type

            if Is_Character_Type (Id) then
               Mark_Non_ALFA_Declaration ("character enumeration type", N);
            end if;

         when N_Signed_Integer_Type_Definition =>
            null;

         when N_Derived_Type_Definition =>
            if Present (Interface_List (Def)) then
               Mark_Non_ALFA_Declaration ("interface", N);
            elsif Present (Record_Extension_Part (Def)) then
               Mark_Non_ALFA_Declaration ("record extension", N, V_Implem);
            else
               Mark_Subtype_Indication_In_Decl (N);
            end if;

         when N_Modular_Type_Definition |
              N_Record_Definition |
              N_Floating_Point_Definition |
              N_Decimal_Fixed_Point_Definition |
              N_Ordinary_Fixed_Point_Definition =>
            Mark_Non_ALFA_Declaration ("type definition", N, V_Implem);

         when N_Access_To_Subprogram_Definition |
              N_Access_To_Object_Definition =>
            Mark_Non_ALFA_Declaration ("access type", N);

         when others =>
            raise Program_Error;
      end case;
   end Mark_Full_Type_Declaration;

   -----------------------------
   -- Mark_Handled_Statements --
   -----------------------------

   procedure Mark_Handled_Statements (N : Node_Id) is
      Handlers : constant List_Id := Exception_Handlers (N);

   begin
      if Present (Handlers) then
         Mark_In_Non_ALFA_Subprogram ("handler", First (Handlers));
      end if;

      Mark_List (Statements (N));
   end Mark_Handled_Statements;

   ---------------------
   -- Mark_Identifier --
   ---------------------

   procedure Mark_Identifier_Or_Expanded_Name (N : Node_Id) is
   begin
      if Is_Entity_Name (N)
        and then not Is_In_ALFA (Entity (N))
      then
         Mark_In_Non_ALFA_Subprogram ("entity", N, From => Entity (N));
      end if;
   end Mark_Identifier_Or_Expanded_Name;

   ---------------------------------
   -- Mark_In_Non_ALFA_Subprogram --
   ---------------------------------

   procedure Mark_In_Non_ALFA_Subprogram
     (Msg : String;
      N   : Node_Id;
      V   : Violation_Kind := V_Other)
   is
      Cur_Scop : constant Scope_Record := Current_Scope;
      Cur_Ent  : constant Entity_Id    := Cur_Scop.Entity;

   begin
      --  If formal proof is forced, then notify the user about the violation

      if Formal_Proof_Currently_Forced then
         Error_Msg_F (Complete_Error_Msg (Msg, Implem => V = V_Implem), N);
      end if;

      case Ekind (Cur_Ent) is

         --  Detect violation in initialization of package-level object

         when Object_Kind =>
            Body_Violations (V).Include (Cur_Ent);

         when E_Package =>
            null;

         --  Detect violation in subprogram declarations and subprogram bodies

         --  If the non-ALFA construct is in a precondition or postcondition,
         --  then mark the subprogram as not in ALFA, because neither the
         --  subprogram nor its callers can be proved formally.

         --  If the non-ALFA construct is in a regular piece of code inside the
         --  body of the subprogram, then mark the subprogram body as not in
         --  ALFA, because the subprogram cannot be proved formally, but its
         --  callers could.

         when Subprogram_Kind =>
            if Cur_Scop.Is_Body then
               Body_Violations (V).Include (Cur_Ent);
            else
               Spec_Violations (V).Include (Cur_Ent);
            end if;

         when others =>
            raise Program_Error;
      end case;
   end Mark_In_Non_ALFA_Subprogram;

   procedure Mark_In_Non_ALFA_Subprogram
     (Msg  : String;
      N    : Node_Id;
      From : Entity_Id)
   is
      Cur_Scop : constant Scope_Record := Current_Scope;
      Cur_Ent  : constant Entity_Id    := Cur_Scop.Entity;

   begin
      --  If formal proof is forced, then notify the user about the violation

      if Formal_Proof_Currently_Forced then
         if (for some V in V_Design =>
               Spec_Violations (V).Contains (From))
         then
            Error_Msg_F (Complete_Error_Msg (Msg, Implem => False), N);
         else
            Error_Msg_F (Complete_Error_Msg (Msg, Implem => True), N);
         end if;
      end if;

      case Ekind (Cur_Ent) is

         --  Detect violation in initialization of package-level object

         when Object_Kind =>
            Inherit_Violations
              (Body_Violations, From => From, To => Cur_Ent);

         when E_Package =>
            null;

         --  Detect violation in subprogram declarations and subprogram bodies

         --  If the non-ALFA construct is in a precondition or postcondition,
         --  then mark the subprogram as not in ALFA, because neither the
         --  subprogram nor its callers can be proved formally.

         --  If the non-ALFA construct is in a regular piece of code inside the
         --  body of the subprogram, then mark the subprogram body as not in
         --  ALFA, because the subprogram cannot be proved formally, but its
         --  callers could.

         when Subprogram_Kind =>
            --  Inherit the violations of entity From

            if Cur_Scop.Is_Body then
               Inherit_Violations
                 (Body_Violations, From => From, To => Cur_Ent);
            else
               Inherit_Violations
                 (Spec_Violations, From => From, To => Cur_Ent);
            end if;

         when others =>
            raise Program_Error;
      end case;
   end Mark_In_Non_ALFA_Subprogram;

   ---------------------------
   -- Mark_Iteration_Scheme --
   ---------------------------

   procedure Mark_Iteration_Scheme (N : Node_Id) is
   begin
      if Present (N)  --  not an infinite loop
        and then Present (Loop_Parameter_Specification (N))
      then
         declare
            LP : constant Node_Id   := Loop_Parameter_Specification (N);
            Id : constant Entity_Id := Defining_Identifier (LP);

         begin
            --  The entity for iterating over a loop is always in ALFA if its
            --  type is in ALFA.

            if not Is_In_ALFA (Etype (Id)) then
               Mark_Non_ALFA_Declaration
                 ("type of loop index", LP, From => Etype (Id));
            end if;
         end;
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

   -------------------------
   -- Mark_Loop_Statement --
   -------------------------

   procedure Mark_Loop_Statement (N : Node_Id) is
      Id  : constant Node_Id := Identifier (N);
      Ent : Entity_Id;

   begin
      if Present (Id) then
         Ent := Entity (Id);

      --  Case of no identifier present. Create a dummy entity for the loop,
      --  so that exits to outter loops are correctly detected as not in ALFA.

      else
         Ent :=
           New_Internal_Entity (E_Loop, Current_Scope.Entity, Sloc (N), 'L');
         Set_Etype (Ent, Standard_Void_Type);
         Set_Parent (Ent, N);
      end if;

      Push_Scope (Ent);
      Mark_Iteration_Scheme (Iteration_Scheme (N));
      Mark_List (Statements (N));
      Pop_Scope;
   end Mark_Loop_Statement;

   -------------------------------
   -- Mark_Non_ALFA_Declaration --
   -------------------------------

   procedure Mark_Non_ALFA_Declaration
     (Msg : String;
      N   : Node_Id;
      V   : Violation_Kind := V_Other) is
   begin
      Spec_Violations (V).Include (Defining_Entity (N));
      Mark_In_Non_ALFA_Subprogram (Msg, N, V);
   end Mark_Non_ALFA_Declaration;

   procedure Mark_Non_ALFA_Declaration
     (Msg  : String;
      N    : Node_Id;
      From : Entity_Id) is
   begin
      Inherit_Violations
        (Spec_Violations, From => From, To => Defining_Entity (N));
      Mark_In_Non_ALFA_Subprogram (Msg, N, From);
   end Mark_Non_ALFA_Declaration;

   -----------------------------
   -- Mark_Object_Declaration --
   -----------------------------

   procedure Mark_Object_Declaration (N : Node_Id) is
      Id   : constant Entity_Id := Defining_Entity (N);
      Expr : constant Node_Id   := Expression (N);
   begin
      --  The object is in ALFA if-and-only-if its type is in ALFA and it is
      --  not aliased.

      if not Is_In_ALFA (Etype (Id)) then
         Mark_Non_ALFA_Declaration ("type of object", N, From => Etype (Id));
      end if;

      if Aliased_Present (N) then
         Mark_Non_ALFA_Declaration ("ALIASED", N);
      end if;

      if Present (Expr) then

         --  If the object is declared in a package, declare a scope for
         --  marking its initialization expression, so that we detect cases
         --  where the object itself is in ALFA but not its initialization.

         if Is_Package_Level_Entity (Id) then
            Push_Scope (Id, Is_Body => True);
         end if;

         Mark (Expr);

         if Is_Package_Level_Entity (Id) then
            Pop_Scope;
         end if;
      end if;
   end Mark_Object_Declaration;

   --------------------------------------
   -- Mark_Object_Renaming_Declaration --
   --------------------------------------

   procedure Mark_Object_Renaming_Declaration (N : Node_Id) is
      E : constant Entity_Id := Entity (Name (N));
   begin
      if not Is_In_ALFA (E) then
         Mark_Non_ALFA_Declaration ("object being renamed", N, From => E);
      end if;
   end Mark_Object_Renaming_Declaration;

   -----------------------
   -- Mark_Package_Body --
   -----------------------

   procedure Mark_Package_Body (N : Node_Id) is
      HSS : constant Node_Id := Handled_Statement_Sequence (N);

   begin
      Push_Scope (Unique_Defining_Entity (N));
      Mark_List (Declarations (N));

      if Present (HSS) then
         Mark (HSS);
      end if;

      Pop_Scope;
   end Mark_Package_Body;

   ------------------------------
   -- Mark_Package_Declaration --
   ------------------------------

   procedure Mark_Package_Declaration (N : Node_Id) is
   begin
      Push_Scope (Unique_Defining_Entity (N));
      Mark (Specification (N));
      Pop_Scope;
   end Mark_Package_Declaration;

   --------------------------------
   -- Mark_Package_Specification --
   --------------------------------

   procedure Mark_Package_Specification (N : Node_Id) is
      Vis_Decls  : constant List_Id := Visible_Declarations (N);
      Priv_Decls : constant List_Id := Private_Declarations (N);

   begin
      if Present (Vis_Decls) then
         Mark_List (Vis_Decls);
      end if;

      if Present (Priv_Decls) then
         Mark_List (Priv_Decls);
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
         --  ALFA subset of Ada:

         --    pragma Annotate (Formal_Proof, MODE);
         --    MODE ::= On | Off

         --    This pragma either forces (mode On) or disables (mode Off)
         --    formal verification of the subprogram in which it is added. When
         --    formal verification is forced, all violations of the the ALFA
         --    subset of Ada present in the subprogram are reported as errors
         --    to the user.

         when Pragma_Annotate =>
            if Chars (Get_Pragma_Arg (Arg1)) = Name_Formal_Proof then
               if List_Length (Pragma_Argument_Associations (N)) /= 2 then
                  Error_Msg_N ("wrong number of arguments for pragma%", N);
                  return;
               end if;

               Arg := Get_Pragma_Arg (Arg2);
               if Nkind (Arg) /= N_Identifier then
                  Error_Msg_N
                    ("argument for pragma% must be an identifier", Arg2);
                  return;
               end if;

               declare
                  Cur_Ent : constant Entity_Id := Current_Scope.Entity;

               begin
                  pragma Assert (Is_Subprogram (Cur_Ent)
                                  or else Ekind (Cur_Ent) = E_Package);

                  --  Check that this is the first occurrence of this pragma
                  --  on the current entity.

                  if Formal_Proof_On.Contains (Cur_Ent)
                    or else Formal_Proof_Off.Contains (Cur_Ent)
                  then
                     Error_Msg_N ("pragma% already given for entity", N);
                     return;
                  end if;

                  if Chars (Arg) = Name_On then
                     Formal_Proof_On.Insert (Cur_Ent);
                  elsif Chars (Arg) = Name_Off then
                     Formal_Proof_Off.Insert (Cur_Ent);
                  else
                     Error_Msg_N
                       ("argument for pragma% must be ON or OFF", Arg2);
                        return;
                  end if;

                  --  Notify user if some ALFA violation occurred before this
                  --  point in Cur_Ent. These violations are not precisly
                  --  located, but this is better than ignoring these
                  --  violations.

                  if Chars (Arg) = Name_On
                    and then (not Is_In_ALFA (Cur_Ent)
                               or else not Body_Is_In_ALFA (Cur_Ent))
                  then
                     Error_Msg_N
                       ("pragma% is placed after violation of ALFA", N);
                     return;
                  end if;
               end;
            end if;

         when others =>
            Mark_In_Non_ALFA_Subprogram ("pragma is not in ALFA", N);
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

      --  RETURN only allowed in ALFA as the last statement in function

      if Nkind (Parent (N)) /= N_Handled_Sequence_Of_Statements
        and then
          (Nkind (Parent (Parent (N))) /= N_Subprogram_Body
            or else Present (Next (N)))
      then
         Mark_In_Non_ALFA_Subprogram ("RETURN not in last position", N);
      end if;
   end Mark_Simple_Return_Statement;

   ---------------------------
   -- Mark_Standard_Package --
   ---------------------------

   procedure Mark_Standard_Package is
   begin
      for S in S_Types loop
         if Standard_Type_Is_In_ALFA (S) then
            Standard_In_ALFA.Insert (Standard_Entity (S));
         end if;
      end loop;

      Standard_In_ALFA.Insert (Universal_Integer);

      Standard_In_ALFA.Insert (Standard_Integer_8);
      Standard_In_ALFA.Insert (Standard_Integer_16);
      Standard_In_ALFA.Insert (Standard_Integer_32);
      Standard_In_ALFA.Insert (Standard_Integer_64);
   end Mark_Standard_Package;

   --------------------------
   -- Mark_Subprogram_Body --
   --------------------------

   procedure Mark_Subprogram_Body (N : Node_Id) is
      Id  : constant Entity_Id := Unique_Defining_Entity (N);
      HSS : constant Node_Id   := Handled_Statement_Sequence (N);

   begin
      Push_Scope (Id);
      Mark_Subprogram_Specification (Specification (N));
      Pop_Scope;

      Push_Scope (Id, Is_Body => True);

      Mark_List (Declarations (N));
      Mark (HSS);

      if Nkind (Specification (N)) = N_Function_Specification then

         --  In ALFA, last statement of a function should be a return

         declare
            Stat : constant Node_Id := Last_Source_Statement (HSS);
         begin
            if Present (Stat)
              and then not Nkind_In (Stat, N_Simple_Return_Statement,
                                     N_Extended_Return_Statement)
            then
               Mark_In_Non_ALFA_Subprogram
                 ("no RETURN at end of function", Stat);
            end if;
         end;

      --  In ALFA, verify that a procedure has no return

      else
         --  Would be nice to point to return statement here, can we
         --  borrow the Check_Returns procedure here ???

         if Return_Present (Id) then
            Mark_In_Non_ALFA_Subprogram ("RETURN in procedure", N);
         end if;
      end if;

      Pop_Scope;
   end Mark_Subprogram_Body;

   ---------------------------------
   -- Mark_Subprogram_Declaration --
   ---------------------------------

   procedure Mark_Subprogram_Declaration (N : Node_Id) is
      PPC : Node_Id;
   begin
      Push_Scope (Defining_Entity (N));
      Mark_Subprogram_Specification (Specification (N));

      PPC := Spec_PPC_List (Defining_Entity (N));
      while Present (PPC) loop
         Mark (PPC);
         PPC := Next_Pragma (PPC);
      end loop;

      Pop_Scope;
   end Mark_Subprogram_Declaration;

   -----------------------------------
   -- Mark_Subprogram_Specification --
   -----------------------------------

   procedure Mark_Subprogram_Specification (N : Node_Id) is
      Designator : constant Entity_Id := Defining_Entity (N);
      Formals    : constant List_Id   := Parameter_Specifications (N);
      Param_Spec : Node_Id;
      Formal     : Entity_Id;

   begin
      if Present (Formals) then
         Param_Spec := First (Formals);
         while Present (Param_Spec) loop
            Formal := Defining_Identifier (Param_Spec);

            --  The parameter is in ALFA if-and-only-if its type is in ALFA

            if not Is_In_ALFA (Etype (Formal)) then
               Mark_Non_ALFA_Declaration
                 ("type of formal", Param_Spec, From => Etype (Formal));
            end if;

            Next (Param_Spec);
         end loop;

         --  If the result type of a subprogram is not in ALFA, then the
         --  subprogram is not in ALFA.

         if Nkind (N) = N_Function_Specification
           and then not Is_In_ALFA (Etype (Designator))
         then
            Mark_In_Non_ALFA_Subprogram
              ("return type", Result_Definition (N),
               From => Etype (Designator));
         end if;
      end if;
   end Mark_Subprogram_Specification;

   -------------------------------------
   -- Mark_Subtype_Indication_In_Decl --
   -------------------------------------

   procedure Mark_Subtype_Indication_In_Decl (N : Node_Id) is
      Sub_Ind : Node_Id;
      T       : Entity_Id;
      Cstr    : Node_Id;

   begin
      if Nkind (N) = N_Subtype_Declaration then
         Sub_Ind := Subtype_Indication (N);
      else
         Sub_Ind := Subtype_Indication (Type_Definition (N));
      end if;

      if Nkind (Sub_Ind) = N_Subtype_Indication then
         T := Etype (Subtype_Mark (Sub_Ind));
      else
         T := Etype (Sub_Ind);
      end if;

      --  Check that the base type is in ALFA

      if not Is_In_ALFA (T) then
         Mark_Non_ALFA_Declaration ("base type", N, From => T);
      end if;

      if Nkind (Sub_Ind) = N_Subtype_Indication then

         Cstr := Constraint (Sub_Ind);
         case Nkind (Cstr) is
            when N_Range_Constraint =>
               if not Is_Static_Range (Range_Expression (Cstr)) then
                  Mark_Non_ALFA_Declaration ("non-static range", N);
               end if;

            when N_Index_Or_Discriminant_Constraint =>

               Cstr := First (Constraints (Cstr));
               while Present (Cstr) loop

                  case Nkind (Cstr) is
                     when N_Identifier | N_Expanded_Name =>
                        if not Is_In_ALFA (Entity (Cstr)) then
                           Mark_Non_ALFA_Declaration
                             ("index type", N, From => Entity (Cstr));
                        end if;

                     when N_Subtype_Indication =>  --  TO DO
                        Mark_Non_ALFA_Declaration ("index type", N, V_Implem);

                     when N_Range =>
                        if not Is_Static_Range (Cstr) then
                           Mark_Non_ALFA_Declaration ("non-static range", N);
                        end if;

                     when N_Discriminant_Association =>
                        Mark_Non_ALFA_Declaration ("discriminant", N);

                     when others =>
                        raise Program_Error;
                  end case;
                  Next (Cstr);
               end loop;

            when others =>  --  TO DO ???
               raise Program_Error;
         end case;
      end if;
   end Mark_Subtype_Indication_In_Decl;

   --------------------------
   -- Mark_Type_Conversion --
   --------------------------

   procedure Mark_Type_Conversion (N : Node_Id) is
      Expr : constant Node_Id := Expression (N);

   begin
      --  Type conversion between scalar types are allowed in ALFA. All other
      --  type conversions are not allowed.

      if not (Is_Scalar_Type (Etype (Expr))
               and then Is_Scalar_Type (Etype (N)))
      then
         Mark_In_Non_ALFA_Subprogram
           ("type conversion not between scalar types", N);
      end if;

      Mark (Expr);
   end Mark_Type_Conversion;

   ---------------
   -- Pop_Scope --
   ---------------

   procedure Pop_Scope is
   begin
      Scope_Stack.Decrement_Last;
   end Pop_Scope;

   ----------------
   -- Push_Scope --
   ----------------

   procedure Push_Scope (E : Entity_Id; Is_Body : Boolean := False) is
   begin
      Scope_Stack.Increment_Last;
      Scope_Stack.Table (Scope_Stack.Last) :=
        Scope_Record'(Entity => E, Is_Body => Is_Body);
   end Push_Scope;

end ALFA.Definition;
