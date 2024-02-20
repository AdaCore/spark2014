------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--      F L O W _ U T I L I T Y . P R O O F _ D E P E N D E N C I E S       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--              Copyright (C) 2024, AdaCore                                 --
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
------------------------------------------------------------------------------

with Gnat2Why.Tables;           use Gnat2Why.Tables;
with Flow_Refinement;           use Flow_Refinement;
with SPARK_Definition.Annotate; use SPARK_Definition.Annotate;
with SPARK_Util.Subprograms;    use SPARK_Util.Subprograms;

with Sinfo.Utils;               use Sinfo.Utils;

package body Flow_Utility.Proof_Dependencies is

   --------------------------------------------
   -- Process_Access_To_Subprogram_Contracts --
   --------------------------------------------

   procedure Process_Access_To_Subprogram_Contracts
     (Typ                : Type_Kind_Id;
      Scop               : Flow_Scope;
      Proof_Dependencies : in out Node_Sets.Set;
      Generating_Globals : Boolean)
   is
      procedure Process_Expressions (L : Node_Lists.List);
      --  Process a list of expressions L to fill FA.Proof_Dependencies

      -------------------------
      -- Process_Expressions --
      -------------------------

      procedure Process_Expressions (L : Node_Lists.List) is
         Funcalls : Call_Sets.Set;
         Unused   : Tasking_Info;
      begin
         for Expr of L loop
            Pick_Generated_Info
              (Expr,
               Scop,
               Funcalls,
               Proof_Dependencies,
               Unused,
               Generating_Globals);
         end loop;

         for Call of Funcalls loop
            Proof_Dependencies.Include (Call.E);
         end loop;
      end Process_Expressions;

      Profile : constant Entity_Id := Directly_Designated_Type (Typ);
   begin
      Process_Expressions
        (Find_Contracts (Profile, Pragma_Precondition));
      Process_Expressions
        (Find_Contracts (Profile, Pragma_Postcondition));
   end Process_Access_To_Subprogram_Contracts;

   ------------------------------
   -- Process_Dispatching_Call --
   ------------------------------

   procedure Process_Dispatching_Call
     (N                  : Node_Id;
      Proof_Dependencies : in out Node_Sets.Set)
   is
      Called_Subp      : constant Entity_Id := Get_Called_Entity (N);
      Dispatching_Type : constant Entity_Id :=
        Base_Retysp
          (SPARK_Util.Subprograms.Find_Dispatching_Type (Called_Subp));
      Descendants      : constant Node_Sets.Set :=
        Get_Descendant_Set (Dispatching_Type);
      Descendant_E     : Entity_Id;
   begin
      for Descendant of Descendants loop
         Descendant_E := Corresponding_Primitive
           (Called_Subp, Descendant);
         Proof_Dependencies.Include (Descendant_E);
      end loop;
   end Process_Dispatching_Call;

   -----------------------
   -- Process_Attribute --
   -----------------------

   procedure Process_Access_Attribute
     (N                  : Node_Id;
      Proof_Dependencies : in out Node_Sets.Set)
   is
      P : constant Node_Id := Prefix (N);
      E : constant Entity_Id :=
        (if Is_Entity_Name (P) then Entity (P)
         else Empty);
   begin
      if Present (E)
        and then Ekind (E) in E_Function | E_Procedure
      then
         Proof_Dependencies.Include (E);
      end if;
   end Process_Access_Attribute;

   -------------------------------------------
   -- Process_Iterable_For_Proof_Annotation --
   -------------------------------------------

   procedure Process_Iterable_For_Proof_Annotation
     (N : Node_Id;
      Proof_Dependencies : in out Node_Sets.Set)
   is
      Typ           : Entity_Id := Etype (Name (N));
      Found         : Boolean;
      Iterable_Info : Iterable_Annotation;
   begin
      --  Proof might transform the quantified expression using the chain of
      --  Model functions associated to the types.

      if Nkind (Parent (Parent (N))) /= N_Loop_Statement then

         loop
            Retrieve_Iterable_Annotation (Typ,
                                          Found,
                                          Iterable_Info);

            if Found
              and then
                Iterable_Info.Kind
                  = SPARK_Definition.Annotate.Model
            then
               Proof_Dependencies.Include
                 (Iterable_Info.Entity);

               Typ := Etype (Iterable_Info.Entity);
            else
               exit;
            end if;
         end loop;

         --  Finally, proof transforms the quantification using
         --  either the Contains function on the type, if it
         --  exists, or the Has_Element and Element functions
         --  otherwise.
         if Found then
            Proof_Dependencies.Include (Iterable_Info.Entity);

         elsif Typ /= Etype (Name (N)) then
            Proof_Dependencies.Include
              (Get_Iterable_Type_Primitive
                 (Typ, Name_Has_Element));
            Proof_Dependencies.Include
              (Get_Iterable_Type_Primitive (Typ, Name_Element));
         end if;
      end if;
   end Process_Iterable_For_Proof_Annotation;

   -------------------------------------
   -- Process_Predicate_And_Invariant --
   -------------------------------------

   procedure Process_Predicate_And_Invariant
     (N                  : Node_Or_Entity_Id;
      Scop               : Flow_Scope;
      Include_Invariant  : Boolean;
      Proof_Dependencies : in out Node_Sets.Set)
   is
      Discard : Node_Sets.Set;
   begin
      Process_Predicate_And_Invariant_Internal
        (N                  => N,
         Scop               => Scop,
         Include_Invariant  => Include_Invariant,
         Proof_Dependencies => Proof_Dependencies,
         Types_Seen         => Discard);
   end Process_Predicate_And_Invariant;

   -----------------------------------
   -- Process_Reclamation_Functions --
   -----------------------------------

   procedure Process_Reclamation_Functions
     (Typ                : Type_Kind_Id;
      Proof_Dependencies : in out Node_Sets.Set)
   is
   begin
      for Part of Get_Reclaimed_Parts (Typ) loop
         declare
            Ent : constant Entity_Id := Get_Reclamation_Entity (Part);
         begin
            --  For now, only collect functions

            if Present (Ent) and then Ekind (Ent) = E_Function then
               Proof_Dependencies.Include (Ent);
            end if;
         end;
      end loop;
   end Process_Reclamation_Functions;

   -----------------------------------
   -- Subprogram_Proof_Dependencies --
   -----------------------------------

   function Subprogram_Proof_Dependencies (E : Entity_Id) return Node_Sets.Set
   is
      Proofdeps : Node_Sets.Set;

      procedure Collect_Proof_Dependencies (Expr : Node_Id);
      --  Collect proof dependencies in expression Expr and put them in Deps

      --------------------------------
      -- Collect_Proof_Dependencies --
      --------------------------------

      procedure Collect_Proof_Dependencies (Expr : Node_Id) is
         Funcalls  : Call_Sets.Set;
         Unused    : Tasking_Info;
      begin
         Pick_Generated_Info
           (Expr,
            Scop               => Get_Flow_Scope (Expr),
            Function_Calls     => Funcalls,
            Proof_Dependencies => Proofdeps,
            Tasking            => Unused,
            Generating_Globals => True);

         for Call of Funcalls loop

            --  We don't pull calls via access-to-subprograms in proof
            --  dependencies.

            if Ekind (Call.E) /= E_Subprogram_Type then
               Proofdeps.Include (Call.E);
            end if;
         end loop;
      end Collect_Proof_Dependencies;

   --  Start of processing for Contract_Proof_Dependencies

   begin
      for Expr of Get_Precondition_Expressions (E) loop
         Collect_Proof_Dependencies (Expr);
      end loop;

      for Expr of Get_Postcondition_Expressions (E, Refined => False)
      loop
         Collect_Proof_Dependencies (Expr);
      end loop;

      --  Process predicates that apply to formals of E

      for F of Get_Explicit_Formals (E) loop
         Process_Predicate_And_Invariant
           (F,
            Get_Flow_Scope (E),
            Is_Globally_Visible (E),
            Proofdeps);
      end loop;

      --  Process predicates that apply to the return type if E is a
      --  function.

      if Ekind (E) = E_Function then
         Process_Predicate_And_Invariant
           (E,
            Get_Flow_Scope (E),
            Is_Globally_Visible (E),
            Proofdeps);
      end if;

      return Proofdeps;
   end Subprogram_Proof_Dependencies;

end Flow_Utility.Proof_Dependencies;
