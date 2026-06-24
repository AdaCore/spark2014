------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--      F L O W _ U T I L I T Y . P R O O F _ D E P E N D E N C I E S       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2024-2026, AdaCore                     --
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

package body Flow_Utility.Proof_Dependencies is

   procedure Process_Aggregate_Annotation
     (E : Entity_Id; Proof_Dependencies : in out Node_Sets.Set)
   with
     Pre  => Is_Type (E),
     Post => Proof_Dependencies'Old.Is_Subset (Of_Set => Proof_Dependencies);

   procedure Process_Dispatching_Subprogram
     (E : Entity_Id; Proof_Dependencies : in out Node_Sets.Set)
   with
     Pre  => Is_Subprogram (E),
     Post => Proof_Dependencies'Old.Is_Subset (Of_Set => Proof_Dependencies);
   --  Fill Proof_Dependencies with all possible callees for dispatching
   --  subprogram E.

   procedure Process_Indirect_Dispatching_Equality
     (Ty : Entity_Id; Proof_Dependencies : in out Node_Sets.Set)
   with
     Pre  => Is_Type (Ty),
     Post => Proof_Dependencies'Old.Is_Subset (Of_Set => Proof_Dependencies);
   --  Fill Proof_Dependencies with all potential candidates for a dispatching
   --  call on the equality of Ty.

   procedure Process_Iterable_For_Proof_Annotation
     (E : Entity_Id; Proof_Dependencies : in out Node_Sets.Set)
   with
     Pre  => Is_Type (E),
     Post => Proof_Dependencies'Old.Is_Subset (Of_Set => Proof_Dependencies);
   --  Fill Proof_Dependencies by analyzing the potential Iterable_For_Proof
   --  annotations associated to N.

   procedure Process_Reclamation_Functions
     (Typ : Entity_Id; Proof_Dependencies : in out Node_Sets.Set)
   with
     Pre  => Is_Type (Typ),
     Post => Proof_Dependencies'Old.Is_Subset (Of_Set => Proof_Dependencies);
   --  Fill Proof_Dependencies with the reclamation functions associated to
   --  all components of Typ.

   --------------------------------------------
   -- Process_Access_To_Subprogram_Contracts --
   --------------------------------------------

   procedure Process_Access_To_Subprogram_Contracts
     (Typ                : Entity_Id;
      Scop               : Flow_Scope;
      Proof_Dependencies : in out Proof_Dependencies_Sets;
      Generating_Globals : Boolean)
   is
      procedure Process_Expressions (L : Node_Lists.List);
      --  Process a list of expressions L to fill Proof_Dependencies

      -------------------------
      -- Process_Expressions --
      -------------------------

      procedure Process_Expressions (L : Node_Lists.List) is
         Funcalls     : Call_Sets.Set;
         Indcalls     : Node_Sets.Set;
         Unused_Locks : Protected_Call_Sets.Set;
      begin
         for Expr of L loop
            Pick_Generated_Info
              (Expr,
               Scop,
               Funcalls,
               Indcalls,
               Proof_Dependencies,
               Unused_Locks,
               Generating_Globals);
         end loop;

         for Call of Funcalls loop
            Proof_Dependencies (Direct_Proof_Dependencies).Include (Call.E);
         end loop;
      end Process_Expressions;

      Profile : constant Entity_Id := Directly_Designated_Type (Typ);
   begin
      Process_Expressions (Find_Contracts (Profile, Pragma_Precondition));
      Process_Expressions (Find_Contracts (Profile, Pragma_Postcondition));
   end Process_Access_To_Subprogram_Contracts;

   ----------------------------------
   -- Process_Aggregate_Annotation --
   ----------------------------------

   procedure Process_Aggregate_Annotation
     (E : Entity_Id; Proof_Dependencies : in out Node_Sets.Set)
   is
      procedure Add_Proof_Dependency (E : Entity_Id)
      with Pre => (if Present (E) then Ekind (E) = E_Function);
      --  Add proof dependency on E, if it is specified for
      --  the container type.

      --------------------------
      -- Add_Proof_Dependency --
      --------------------------

      procedure Add_Proof_Dependency (E : Entity_Id) is
      begin
         if Present (E) then
            Proof_Dependencies.Include (E);
         end if;
      end Add_Proof_Dependency;

      Annot : constant Aggregate_Annotation := Get_Aggregate_Annotation (E);

   begin

      Add_Proof_Dependency (Annot.Capacity);

      case Annot.Kind is
         when Sets  =>
            Add_Proof_Dependency (Annot.Contains);
            Add_Proof_Dependency (Annot.Equivalent_Elements);
            Add_Proof_Dependency (Annot.Sets_Length);

         when Maps  =>
            Add_Proof_Dependency (Annot.Has_Key);
            Add_Proof_Dependency (Annot.Default_Item);
            Add_Proof_Dependency (Annot.Equivalent_Keys);
            Add_Proof_Dependency (Annot.Maps_Length);
            Add_Proof_Dependency (Annot.Maps_Length);

         when Seqs  =>
            Add_Proof_Dependency (Annot.Seqs_Get);
            Add_Proof_Dependency (Annot.First);
            Add_Proof_Dependency (Annot.Last);

         when Model =>
            Add_Proof_Dependency (Annot.Model);
      end case;
   end Process_Aggregate_Annotation;

   ------------------------------------
   -- Process_Dispatching_Subprogram --
   ------------------------------------

   procedure Process_Dispatching_Subprogram
     (E : Entity_Id; Proof_Dependencies : in out Node_Sets.Set)
   is
      Dispatching_Type : constant Entity_Id :=
        Base_Retysp (SPARK_Util.Subprograms.Find_Dispatching_Type (E));
      Descendants      : constant Node_Sets.Set :=
        Get_Descendant_Set (Dispatching_Type);
      Descendant_E     : Entity_Id;
   begin
      for Descendant of Descendants loop
         Descendant_E := Corresponding_Primitive (E, Descendant);
         Proof_Dependencies.Include (Descendant_E);
      end loop;
   end Process_Dispatching_Subprogram;

   -------------------------------------------
   -- Process_Indirect_Dispatching_Equality --
   -------------------------------------------

   procedure Process_Indirect_Dispatching_Equality
     (Ty : Entity_Id; Proof_Dependencies : in out Node_Sets.Set)
   is

      procedure Traverse_Ancestors;
      --  Traverse ancestors of type Ty to pull called equalities in proof
      --  dependencies.

      ------------------------
      -- Traverse_Ancestors --
      ------------------------

      procedure Traverse_Ancestors is
         Base_Ty   : Type_Kind_Id := Base_Retysp (Ty);
         Parent_Ty : Opt_Type_Kind_Id := Parent_Retysp (Base_Ty);
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

   -------------------------------------------
   -- Process_Iterable_For_Proof_Annotation --
   -------------------------------------------

   procedure Process_Iterable_For_Proof_Annotation
     (E : Entity_Id; Proof_Dependencies : in out Node_Sets.Set)
   is
      Typ           : Entity_Id := E;
      Found         : Boolean;
      Iterable_Info : Iterable_Annotation;
   begin

      loop
         Retrieve_Iterable_Annotation (Typ, Found, Iterable_Info);

         if Found and then Iterable_Info.Kind = SPARK_Definition.Annotate.Model
         then
            Proof_Dependencies.Include (Iterable_Info.Entity);

            Typ := Etype (Iterable_Info.Entity);
         else
            exit;
         end if;
      end loop;

      --  Finally, proof transforms the quantification using
      --  either the Contains function on the type, if it
      --  exists, or the Has_Element and Element or Constant_Reference
      --  functions otherwise.

      if Found then
         Proof_Dependencies.Include (Iterable_Info.Entity);

      elsif Typ /= E then
         Proof_Dependencies.Include
           (Get_Iterable_Type_Primitive (Typ, Name_Has_Element));

         declare
            Element : Entity_Id :=
              Get_Iterable_Type_Primitive (Typ, Name_Element);
         begin
            if No (Element) then
               Element :=
                 Get_Iterable_Type_Primitive (Typ, Name_Constant_Reference);
            end if;
            Proof_Dependencies.Include (Element);
         end;
      end if;
   end Process_Iterable_For_Proof_Annotation;

   --------------------------------
   -- Process_Proof_Dependencies --
   --------------------------------

   procedure Process_Proof_Dependencies
     (Proof_Dependencies : Proof_Dependencies_Sets; Result : out Node_Sets.Set)
   is
   begin
      for E of Proof_Dependencies (Direct_Proof_Dependencies) loop
         Result.Include (E);
      end loop;

      for E of Proof_Dependencies (Aggregate_Annotations) loop
         Process_Aggregate_Annotation (E, Result);
      end loop;

      for E of Proof_Dependencies (Dispatching_Called_Subprograms) loop
         Process_Dispatching_Subprogram (E, Result);
      end loop;

      for E of Proof_Dependencies (Indirect_Dispatching_Equalities) loop
         Process_Indirect_Dispatching_Equality (E, Result);
      end loop;

      for E of Proof_Dependencies (Iterable_For_Proof_Annotations) loop
         Process_Iterable_For_Proof_Annotation (E, Result);
      end loop;

      for E of Proof_Dependencies (Reclaimed_Types) loop
         Process_Reclamation_Functions (E, Result);
      end loop;
   end Process_Proof_Dependencies;

   ----------------------------
   -- Process_Type_Contracts --
   ----------------------------

   procedure Process_Type_Contracts
     (Typ                : Entity_Id;
      Scop               : Flow_Scope;
      Include_Invariant  : Boolean;
      Proof_Dependencies : in out Proof_Dependencies_Sets)
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
     (Typ : Entity_Id; Proof_Dependencies : in out Node_Sets.Set) is
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

   ------------------------------
   -- Union_Proof_Dependencies --
   ------------------------------

   procedure Union_Proof_Dependencies
     (Target : in out Proof_Dependencies_Sets;
      Source : Proof_Dependencies_Sets) is
   begin
      for Kind in Proof_Dependency_Kind loop
         Target (Kind).Union (Source (Kind));
      end loop;
   end Union_Proof_Dependencies;
end Flow_Utility.Proof_Dependencies;
