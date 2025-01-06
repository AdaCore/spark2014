------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--      F L O W _ U T I L I T Y . P R O O F _ D E P E N D E N C I E S       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2024-2025, AdaCore                     --
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
         Indcalls : Node_Sets.Set;
         Unused   : Tasking_Info;
      begin
         for Expr of L loop
            Pick_Generated_Info
              (Expr,
               Scop,
               Funcalls,
               Indcalls,
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

   -------------------------------------------
   -- Process_Indirect_Dispatching_Equality --
   -------------------------------------------

   procedure Process_Indirect_Dispatching_Equality
     (Ty                 : Node_Id;
      Proof_Dependencies : in out Node_Sets.Set)
   is

      procedure Traverse_Ancestors;
      --  Traverse ancestors of type Ty to pull called equalities in proof
      --  dependencies.

      ------------------------
      -- Traverse_Ancestors --
      ------------------------

      procedure Traverse_Ancestors is
         Base_Ty   : Type_Kind_Id := Base_Retysp (Ty);
         Parent_Ty : Opt_Type_Kind_Id :=
           Parent_Retysp (Base_Ty);
      begin
         loop
            if not Use_Predefined_Equality_For_Type (Base_Ty) then
               Proof_Dependencies.Include (Get_User_Defined_Eq (Base_Ty));
               exit;
            end if;

            Base_Ty := Parent_Ty;
            Parent_Ty := Parent_Retysp (Base_Ty);

            exit when No (Parent_Ty) or else Base_Ty = Parent_Ty;
         end loop;
      end Traverse_Ancestors;

      Descendants  : constant Node_Sets.Set := Get_Descendant_Set (Ty);
      Descendant_E : Entity_Id;
   begin

      --  Pull user-defined equalities from descendants of type Ty

      for Descendant of Descendants loop
         if not Use_Predefined_Equality_For_Type (Descendant) then
            Descendant_E := Get_User_Defined_Eq (Descendant);
            Proof_Dependencies.Include (Descendant_E);
         end if;
      end loop;

      --  Pull user-defined equalities from ancestors of type Ty

      Traverse_Ancestors;
   end Process_Indirect_Dispatching_Equality;

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

   ----------------------------
   -- Process_Type_Contracts --
   ----------------------------

   procedure Process_Type_Contracts
     (Typ                : Type_Kind_Id;
      Scop               : Flow_Scope;
      Include_Invariant  : Boolean;
      Proof_Dependencies : in out Node_Sets.Set)
   is
      Types_Discard, Const_Discard : Node_Sets.Set;
   begin
      Process_Type_Contracts_Internal
        (Typ                => Typ,
         Scop               => Scop,
         Include_Invariant  => Include_Invariant,
         Proof_Dependencies => Proof_Dependencies,
         Types_Seen         => Types_Discard,
         Constants_Seen     => Const_Discard);
   end Process_Type_Contracts;

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
end Flow_Utility.Proof_Dependencies;
