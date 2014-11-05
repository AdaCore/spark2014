------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             W H Y - I N T E R                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2014, AdaCore                   --
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

with Atree;         use Atree;
with Einfo;         use Einfo;
with Namet;         use Namet;
with SPARK_Xrefs;   use SPARK_Xrefs;
with Sem_Util;      use Sem_Util;
with Sinfo;         use Sinfo;
with Snames;        use Snames;
with Stand;         use Stand;
with String_Utils;  use String_Utils;

with Constant_Tree;

with SPARK_Definition;       use SPARK_Definition;
with SPARK_Frame_Conditions; use SPARK_Frame_Conditions;
with SPARK_Util;             use SPARK_Util;

with Flow_Utility;

with Gnat2Why.Nodes;      use Gnat2Why.Nodes;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Atree.Traversal; use Why.Atree.Traversal;
with Why.Conversions;     use Why.Conversions;
with Why.Gen.Names;       use Why.Gen.Names;

---------------
-- Why.Inter --
---------------

package body Why.Inter is

   -----------------------
   -- Local Subprograms --
   -----------------------

   subtype N_Has_Theory is Node_Kind with
     Static_Predicate => N_Has_Theory in N_String_Literal |
                                         N_Aggregate;
   --  Subtype of nodes (instead of entities) which have an associated theory,
   --  and should be treated specially.

   package Type_Hierarchy is
     new Constant_Tree (EW_Type, EW_Unit);

   function Extract_Object_Name (Obj : String) return String;
   --  Extract the name after the last "__"; return Obj when the string does
   --  not contain "__". This is useful to determine the user name of an Ada
   --  entity when all we have is its fully scoped name (for hidden effects of
   --  other units).

   function Compute_Ada_Node_Set (S : Why_Node_Sets.Set) return Node_Sets.Set;
   --  transform a module set into a node set by taking the Ada_Node of each
   --  element.

   function Get_EW_Term_Type (N : Node_Id) return EW_Type;

   function EW_Abstract_Shared
     (N    : Node_Id;
      Kind : EW_Type) return W_Type_Id
     with Pre => Kind in EW_Abstract | EW_Split;
   --  Build an type node from an Ada type node, either of kind Split or
   --  Abstract

   function New_Kind_Base_Type (E : Entity_Id; Kind : EW_Type) return W_Type_Id
     with Pre => Kind in EW_Abstract | EW_Split;

   --------------------------
   -- Compute_Ada_Node_Set --
   --------------------------

   function Compute_Ada_Node_Set (W : Why_Node_Id) return Node_Sets.Set is
   begin
      return Compute_Ada_Node_Set (Compute_Module_Set (W));
   end Compute_Ada_Node_Set;

   function Compute_Ada_Node_Set (S : Why_Node_Sets.Set) return Node_Sets.Set
   is
      Result : Node_Sets.Set := Node_Sets.Empty_Set;
   begin
      for M of S loop
         declare
            N : constant Node_Id := Get_Ada_Node (M);
         begin
            if Present (N) then
               Result.Include (N);
            end if;
         end;
      end loop;
      return Result;
   end Compute_Ada_Node_Set;

   ------------------------
   -- Compute_Module_Set --
   ------------------------

   function Compute_Module_Set (W : Why_Node_Id) return Why_Node_Sets.Set is
      use Why_Node_Sets;

      type Search_State is new Traversal_State with record
         S : Set;
      end record;

      procedure Identifier_Pre_Op
        (State : in out Search_State;
         Node  : W_Identifier_Id);

      procedure Name_Pre_Op
        (State : in out Search_State;
         Node  : W_Name_Id);

      procedure Relation_Pre_Op
        (State : in out Search_State;
         Node  : W_Relation_Id);

      procedure Unary_Op_Pre_Op
        (State : in out Search_State;
         Node  : W_Unary_Op_Id);

      procedure Binary_Op_Pre_Op
        (State : in out Search_State;
         Node  : W_Binary_Op_Id);

      procedure Integer_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Integer_Constant_Id);

      procedure Real_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Real_Constant_Id);

      procedure Fixed_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Fixed_Constant_Id);

      procedure Handle_Op (S : in out Set; Op : EW_Type);
      --  add needed modules for basic scalar (unary and binary +,- etc) to the
      --  state

      ----------------------
      -- Binary_Op_Pre_Op --
      ----------------------

      procedure Binary_Op_Pre_Op
        (State : in out Search_State;
         Node  : W_Binary_Op_Id) is
      begin
         Handle_Op (State.S, Get_Op_Type (Node));
      end Binary_Op_Pre_Op;

      ---------------------------
      -- Fixed_Constant_Pre_Op --
      ---------------------------

      procedure Fixed_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Fixed_Constant_Id) is
         pragma Unreferenced (Node);
      begin
         State.S.Include (+Int_Module);
      end Fixed_Constant_Pre_Op;

      ---------------
      -- Handle_Op --
      ---------------

      procedure Handle_Op (S : in out Set; Op : EW_Type) is
      begin
         case Op is
            when EW_Int | EW_Fixed =>
               S.Include (+Integer_Module);
               S.Include (+Int_Module);
            when EW_Real =>
               S.Include (+Floating_Module);
               S.Include (+RealInfix);
            when others =>
               null;
         end case;
      end Handle_Op;

      -----------------------
      -- Identifier_Pre_Op --
      -----------------------

      procedure Identifier_Pre_Op
        (State : in out Search_State;
         Node  : W_Identifier_Id)
      is
         Module : constant W_Module_Id := Get_Module (Node);
      begin
         if Module /= Why_Empty then
            State.S.Include (+Module);
         end if;
      end Identifier_Pre_Op;

      -----------------------------
      -- Integer_Constant_Pre_Op --
      -----------------------------

      procedure Integer_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Integer_Constant_Id) is
         pragma Unreferenced (Node);
      begin
         State.S.Include (+Int_Module);
      end Integer_Constant_Pre_Op;

      -----------------
      -- Name_Pre_Op --
      -----------------

      procedure Name_Pre_Op
        (State : in out Search_State;
         Node  : W_Name_Id)
      is
         Module : constant W_Module_Id := Get_Module (Node);
      begin
         if Module /= Why_Empty then
            State.S.Include (+Module);
         end if;
      end Name_Pre_Op;

      --------------------------
      -- Real_Constant_Pre_Op --
      --------------------------

      procedure Real_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Real_Constant_Id) is
         pragma Unreferenced (Node);
      begin
         State.S.Include (+RealInfix);
      end Real_Constant_Pre_Op;

      ---------------------
      -- Relation_Pre_Op --
      ---------------------

      procedure Relation_Pre_Op
        (State : in out Search_State;
         Node  : W_Relation_Id) is
      begin
         Handle_Op (State.S, Get_Op_Type (Node));
      end Relation_Pre_Op;

      ---------------------
      -- Unary_Op_Pre_Op --
      ---------------------

      procedure Unary_Op_Pre_Op
        (State : in out Search_State;
         Node  : W_Unary_Op_Id) is
      begin
         Handle_Op (State.S, Get_Op_Type (Node));
      end Unary_Op_Pre_Op;

      SS : Search_State := (Control => Continue, S => Empty_Set);

   --  Start of Compute_Ada_Nodeset

   begin
      Traverse (SS, +W);
      return SS.S;
   end Compute_Module_Set;

   ------------------------
   -- Add_Effect_Imports --
   ------------------------

   procedure Add_Effect_Imports (T : W_Theory_Declaration_Id;
                                 S : Name_Set.Set)
   is
   begin
      for Var of S loop
         if not (Is_Heap_Variable (Var)) then
            declare
               S : constant String := Capitalize_First (Var.all);
            begin
               Add_With_Clause (T,
                                New_Module (File => No_Name, Name => NID (S)),
                                EW_Clone_Default);
            end;
         end if;
      end loop;
   end Add_Effect_Imports;

   ------------------------
   -- Add_Effect_Imports --
   ------------------------

   procedure Add_Effect_Imports (P : Why_Section;
                                 S : Name_Set.Set)
   is
   begin
      Add_Effect_Imports (P.Cur_Theory, S);
   end Add_Effect_Imports;

   --------------------------
   -- Add_Extra_Dependency --
   --------------------------

   procedure Add_Extra_Dependency
     (Defined_Entity : Entity_Id;
      New_Dependency : Entity_Id) is
   begin
      Add_To_Graph (Map  => Entity_Dependencies,
                    From => Defined_Entity,
                    To   => New_Dependency);
   end Add_Extra_Dependency;

   ------------------------
   -- Add_Use_For_Entity --
   ------------------------

   procedure Add_Use_For_Entity
     (P               : Why_Section;
      N               : Entity_Id;
      Use_Kind        : EW_Clone_Type := EW_Clone_Default;
      With_Completion : Boolean := True)
   is
      Module      : constant W_Module_Id := E_Module (N);
   --  Start of Add_Use_For_Entity

   begin
      --  In the few special cases for which the Full_Name of N is not based on
      --  its Unique_Name, the corresponding theories are standard ones (dealt
      --  with separately). Return in that case, to avoid generating wrong
      --  includes based on a non-unique Full_Name.

      if Full_Name_Is_Not_Unique_Name (N) then
         return;
      end if;

      Add_With_Clause (P, Module, Use_Kind);

      if With_Completion
        and then Nkind (N) in N_Entity
        and then not Entity_In_External_Axioms (N)
      then
         Add_With_Clause (P, E_Axiom_Module (N), Use_Kind);
      end if;
   end Add_Use_For_Entity;

   ---------------------
   -- Add_With_Clause --
   ---------------------

   procedure Add_With_Clause (T        : W_Theory_Declaration_Id;
                              Module   : W_Module_Id;
                              Use_Kind : EW_Clone_Type;
                              Th_Type  : EW_Theory_Type := EW_Module) is
      Use_Kind2 : EW_Clone_Type := Use_Kind;
   begin
      if Module = Int_Module
        or else Module = RealInfix
        or else Module = Main_Module
      then
         Use_Kind2 := EW_Import;
      end if;
      Theory_Declaration_Append_To_Includes
        (T,
         New_Include_Declaration
           (Module   => Module,
            Use_Kind => Use_Kind2,
            Kind     => Th_Type));
   end Add_With_Clause;

   procedure Add_With_Clause (P        : Why_Section;
                              Module   : W_Module_Id;
                              Use_Kind : EW_Clone_Type;
                              Th_Type  : EW_Theory_Type := EW_Module) is
   begin
      Add_With_Clause (P.Cur_Theory, Module, Use_Kind, Th_Type);
   end Add_With_Clause;

   -------------------
   -- Base_Why_Type --
   -------------------

   function Base_Why_Type (W : W_Type_Id) return W_Type_Id is
      Kind : constant EW_Type := Get_Base_Type (W);
   begin
      case Kind is
         when EW_Abstract =>
            return Base_Why_Type (Get_Ada_Node (+W));
         when others =>
            return W;
      end case;
   end Base_Why_Type;

   function Base_Why_Type (N : Node_Id) return W_Type_Id is

      E   : constant EW_Type := Get_EW_Term_Type (N);
      Typ : constant Entity_Id := Etype (N);
   begin
      case E is
         when EW_Abstract =>

            --  For a record type, we take as base type its root type, in order
            --  to allow conversions between all types that derive from it.

            --  Record in units with external axiomatization may have a root
            --  type not in SPARK. Conversions between these record types is
            --  expected to be noop, so the base type is taken to be the same
            --  as the type in that case.

            if Fullview_Not_In_SPARK (Typ) then
               return EW_Abstract (Get_First_Ancestor_In_SPARK (Typ));
            elsif Has_Record_Type (Typ) then
               return EW_Abstract (Root_Record_Type (Typ));
            else
               return EW_Abstract (Typ);
            end if;
         when others =>
            return Why_Types (E);
      end case;
   end Base_Why_Type;

   function Base_Why_Type (Left, Right : W_Type_Id) return W_Type_Id
   is
   begin
      return LCA (Base_Why_Type (Left), Base_Why_Type (Right));
   end Base_Why_Type;

   function Base_Why_Type (Left, Right : Node_Id) return W_Type_Id is
   begin
      return Base_Why_Type (Base_Why_Type (Left), Base_Why_Type (Right));
   end Base_Why_Type;

   ------------------
   -- Close_Theory --
   ------------------

   procedure Close_Theory
     (P              : in out Why_Section;
      Kind           : Theory_Kind;
      Defined_Entity : Entity_Id := Empty)
   is
      use Why_Node_Sets;
      S : constant Set := Compute_Module_Set (+P.Cur_Theory);

      function Is_Relevant_Node_For_Imports
        (N             : Node_Id;
         Filter_Entity : Node_Id := Empty) return Boolean;
      --  Returns True if N is relevant for theory imports. Filter_Entity is a
      --  node that should not be considered in these imports.

      procedure Add_Definition_Imports
        (Filter_Module : W_Module_Id := Why_Empty);
      --  Adds imports for the definitions of symbols in S

      procedure Add_Axiom_Imports (S : Node_Sets.Set);
      --  Adds imports for the axioms of symbols in S

      procedure Record_Dependencies (Defined_Entity : Entity_Id);
      --  Records the dependencies between Defined_Entity and the nodes in S

      -----------------------
      -- Add_Axiom_Imports --
      -----------------------

      procedure Add_Axiom_Imports (S : Node_Sets.Set) is
      begin
         for N of S loop
            if not (Nkind (N) in N_Entity)
              or else not Entity_In_External_Axioms (N)
            then
               Add_With_Clause (P,
                                E_Axiom_Module (N),
                                EW_Clone_Default);
            end if;
         end loop;
      end Add_Axiom_Imports;

      ----------------------------
      -- Add_Definition_Imports --
      ----------------------------

      procedure Add_Definition_Imports
        (Filter_Module : W_Module_Id := Why_Empty) is
      begin
         for M of S loop
            if +M /= Filter_Module then
               Add_With_Clause (P, W_Module_Id (M), EW_Clone_Default);
            end if;
         end loop;
      end Add_Definition_Imports;

      ----------------------------------
      -- Is_Relevant_Node_For_Imports --
      ----------------------------------

      --  Here we need to consider entities and some non-entities such as
      --  string literals. We do *not* consider the Filter_Entity, nor its
      --  Full_View. Loop parameters are a bit special, we want to deal with
      --  them only if they are from loop, but not from a quantifier.

      function Is_Relevant_Node_For_Imports
        (N             : Node_Id;
         Filter_Entity : Node_Id := Empty) return Boolean is
      begin
         return N /= Filter_Entity
           and then
             (if Nkind (N) in N_Entity then Ekind (N) /= E_Void)
           and then
             (if Nkind (N) in N_Entity and then Is_Full_View (N) then
                Partial_View (N) /= Filter_Entity)
           and then
             (if Nkind (N) in N_Entity
                and then Ekind (N) = E_Loop_Parameter
              then not Is_Quantified_Loop_Param (N));
      end Is_Relevant_Node_For_Imports;

      -------------------------
      -- Record_Dependencies --
      -------------------------

      procedure Record_Dependencies (Defined_Entity : Entity_Id) is
      begin
         for M of S loop
            if Is_Relevant_Node_For_Imports (Get_Ada_Node (M)) then
               Add_To_Graph (Entity_Dependencies,
                             Defined_Entity,
                             Get_Ada_Node (M));
            end if;
         end loop;
      end Record_Dependencies;

   --  Start of Close_Theory

   begin
      Add_With_Clause (P, Main_Module, EW_Import);

      case Kind is
         --  case 1: a standalone theory with no imports

         when Standalone_Theory =>
            null;

         --  case 2: a theory defining the symbols for Defined_Entity

         --  Add dependencies between Defined_Entity and all other entities
         --  used in the its definition. This will be used when importing the
         --  axiom theories in case 4 below.

         --  Add imports for other symbols used in the definition of
         --  Defined_Entity. Make sure not to import the current theory
         --  defining Defined_Entity itself. Add standard imports.

         when Definition_Theory =>
            if Present (Defined_Entity) then
               Record_Dependencies (Defined_Entity);
            end if;
            Add_Definition_Imports
              (Filter_Module => E_Module (Defined_Entity));

         --  case 3: a theory giving axioms for Defined_Entity

         --  Add dependencies between Defined_Entity and all other entities
         --  used in the its axioms. This will be used when importing the
         --  axiom theories in case 4 below.

         --  Add imports for all symbols used in the axioms of Defined_Entity.
         --  The definition theory for Defined_Entity will be one of those. Add
         --  standard imports.

         when Axiom_Theory =>
            pragma Assert (Present (Defined_Entity));
            Record_Dependencies (Defined_Entity);
            Add_Definition_Imports;

         --  case 4: a theory for generating VCs

         --  Add to S the set of all axioms used transitively to define symbols
         --  in the current theory. Add imports for all symbols used and their
         --  axioms. Add standard imports.

         when VC_Generation_Theory =>
            Add_Definition_Imports;
            declare
               NS : Node_Sets.Set := Compute_Ada_Node_Set (S);
            begin
               NS.Union (Get_Graph_Closure (Entity_Dependencies, NS));
               Add_Axiom_Imports (NS);
            end;
      end case;

      File_Append_To_Theories (P.File, +P.Cur_Theory);
      P.Cur_Theory := Why_Empty;
   end Close_Theory;

   --------------------
   -- Discard_Theory --
   --------------------

   procedure Discard_Theory (P : in out Why_Section) is
   begin
      P.Cur_Theory := Why_Empty;
   end Discard_Theory;

   ---------------------
   -- Dispatch_Entity --
   ---------------------

   function Dispatch_Entity (E : Entity_Id) return Why_Section_Enum is
   begin
      --  Theories for nodes that are not entities may depend on constants
      --  declared in modules for variables (bounds of arrays for example).
      --  Since they can only be used in expressions, we only need them for
      --  subprogram's contracts and VCs which are all stored in WF_Main.

      if Nkind (E) in N_Has_Theory then
         return WF_Context;
      end if;

      case Ekind (E) is
         when Named_Kind  =>
            return WF_Context;

         when Subprogram_Kind | E_Subprogram_Body =>
            declare
               Decl_E : constant Entity_Id := Unique_Entity (E);
            begin
               --  Functions without read/write global effects are declared
               --  in the "type" Why files instead of the "context" Why files,
               --  so that they can be used as parameters of generics whose
               --  axiomatization in Why is written manually (example: formal
               --  containers).

               if Ekind (E) = E_Function
                 and then not Flow_Utility.Has_Proof_Global_Reads
                 (Decl_E,
                  Classwide => True)
                 and then not Flow_Utility.Has_Proof_Global_Writes
                 (Decl_E,
                  Classwide => True)
               then
                  return WF_Pure;
               else
                  return WF_Context;
               end if;
            end;

         when Object_Kind =>

            --  Constants are defined in type files. Their defining axiom, if
            --  any, is defined as a completion in the type or context file.

            if not Is_Mutable_In_Why (E) then
               return WF_Pure;

            elsif Ekind (E) = E_Discriminant
              and then Is_External_Axioms_Discriminant (E)
            then
               return WF_Context;
            else
               return WF_Variables;
            end if;

         when Type_Kind =>
            return WF_Pure;

         when E_Package =>
            return WF_Pure;

         when E_Loop =>
            return WF_Context;

         when E_Abstract_State =>
            return WF_Variables;

         when others =>
            raise Program_Error;
      end case;
   end Dispatch_Entity;

   --------------------------------
   -- Dispatch_Entity_Completion --
   --------------------------------

   function Dispatch_Entity_Completion (E : Entity_Id)
                                        return Why_Section_Enum is
      pragma Unreferenced (E);
   begin

      --  Completion modules are only used by VC generation modules, so they
      --  are not needed earlier. The VC generation modules are generated
      --  later, so the completions will be available at that point.

      return WF_Main;
   end Dispatch_Entity_Completion;

   --------
   -- Eq --
   --------

   function Eq (Left, Right : Entity_Id) return Boolean is
   begin
      if No (Left) or else No (Right) then
         return Left = Right;
      else
         return
           Full_Name (Left) = Full_Name (Right);
      end if;
   end Eq;

   function Eq_Base (Left, Right : W_Type_Id) return Boolean is
   begin
      if Left = Right then
         return True;
      end if;
      declare
         N1 : constant W_Name_Id := Get_Name (+Left);
         N2 : constant W_Name_Id := Get_Name (+Right);
      begin
         if N1 = N2 then
            return True;
         end if;
         declare
            M1 : constant W_Module_Id := Get_Module (N1);
            M2 : constant W_Module_Id := Get_Module (N2);
         begin
            if M1 = M2 or else
              (M1 /= Why_Empty
               and then M2 /= Why_Empty
               and then Get_Name (M1) = Get_Name (M2))
            then
               return Get_Symbol (N1) = Get_Symbol (N2);
            else
               return False;
            end if;
         end;
      end;
   end Eq_Base;

   ------------------
   -- Eq_Base_Type --
   ------------------

   function Eq_Base_Type (Left, Right : W_Type_Id) return Boolean is
   begin
      return Left = Right or else Eq_Base (Left, Right);
   end Eq_Base_Type;

   -----------------
   -- EW_Abstract --
   -----------------

   function EW_Abstract (N : Node_Id) return W_Type_Id is
   begin
      return EW_Abstract_Shared (N, EW_Abstract);
   end EW_Abstract;

   ------------------------
   -- EW_Abstract_Shared --
   ------------------------

   function EW_Abstract_Shared
     (N    : Node_Id;
      Kind : EW_Type) return W_Type_Id is
   begin
      if Is_Standard_Boolean_Type (N) then
         return EW_Bool_Type;

      elsif N = Universal_Fixed then
         return EW_Real_Type;

      --  Classwide types are translated as their corresponding specific tagged
      --  types.

      elsif Ekind (N) in E_Class_Wide_Type | E_Class_Wide_Subtype then
         return EW_Abstract_Shared (Corresponding_Tagged (N), Kind);

      elsif Ekind (N) in Private_Kind
        or else Has_Private_Declaration (N)
      then
         if Entity_In_SPARK (N) and then not Fullview_Not_In_SPARK (N) then
            if MUT (N) = N then
               return New_Kind_Base_Type (N, Kind);
            else
               return EW_Abstract (MUT (N));
            end if;
         else
            return New_Kind_Base_Type (N, Kind);
         end if;

      elsif not Entity_In_SPARK (N) then

         --  This can happen for globals

         return EW_Private_Type;

      else
         return New_Kind_Base_Type (N, Kind);
      end if;
   end EW_Abstract_Shared;

   --------------
   -- EW_Split --
   --------------

   function EW_Split (N : Node_Id) return W_Type_Id is
   begin
      return EW_Abstract_Shared (N, EW_Split);
   end EW_Split;

   -------------------------
   -- Extract_Object_Name --
   -------------------------

   function Extract_Object_Name (Obj : String) return String is
      Index : Integer := Obj'Last;
   begin
      while Index > Obj'First loop
         if Obj (Index) = '_' then
            if Obj (Index - 1) = '_' then
               exit;
            else
               Index := Index - 2;
            end if;
         else
            Index := Index - 1;
         end if;
      end loop;
      if Index in Obj'Range and then Obj (Index) = '_' then
         return Obj (Index + 1 .. Obj'Last);
      else
         return Obj;
      end if;
   end Extract_Object_Name;

   function Get_EW_Type (T : Node_Id) return EW_Type is
      E : constant EW_Type := Get_EW_Term_Type (T);
   begin
      case E is
         when EW_Scalar =>
            return E;
         when others =>
            return EW_Abstract;
      end case;
   end Get_EW_Type;

   ----------------------
   -- Get_EW_Term_Type --
   ----------------------

   function Get_EW_Term_Type (N : Node_Id) return EW_Type is
      Ty : Node_Id := N;
   begin
      if Nkind (N) /= N_Defining_Identifier
        or else not (Ekind (N) in Type_Kind)
      then
         Ty := Etype (N);
      end if;

      case Ekind (Ty) is
         when Fixed_Point_Kind =>
            return EW_Fixed;

         when Float_Kind =>
            return EW_Real;

         when Discrete_Kind =>
            --  In the case of Standard.Boolean, the base type 'bool' is
            --  used directly. For its subtypes, however, an abstract type
            --  representing a signed int is generated, just like for any
            --  other enumeration subtype.
            --  ??? It would make sense to use a bool-based abstract
            --  subtype in this case, and it should be rather easy to
            --  make this change as soon as theory cloning would work
            --  in Why 3. No point in implementing this improvement
            --  before that, as we have seen no cases where this was a
            --  problem for the prover.

            if Is_Standard_Boolean_Type (Ty) then
               return EW_Bool;
            elsif Ty = Universal_Fixed then
               return EW_Real;
            else
               return EW_Int;
            end if;

         when Private_Kind =>
            if Fullview_Not_In_SPARK (Ty) then
               return EW_Abstract;
            else
               return Get_EW_Term_Type (MUT (Ty));
            end if;

         when others =>
            return EW_Abstract;
      end case;
   end Get_EW_Term_Type;

   -------------------------
   -- Is_Array_Conversion --
   -------------------------

   function Is_Array_Conversion (Left, Right : W_Type_Id) return Boolean
   is (Get_Base_Type (Base_Why_Type (Left)) in EW_Abstract | EW_Split and then
       Get_Base_Type (Base_Why_Type (Right)) in EW_Abstract | EW_Split and then
       Has_Array_Type (Get_Ada_Node (+Left)) and then
       Has_Array_Type (Get_Ada_Node (+Right)));

   ------------------------------
   -- Is_Private_Conversion --
   ------------------------------

   function Is_Private_Conversion (Left, Right : W_Type_Id) return Boolean
   is (Get_Base_Type (Base_Why_Type (Left)) in EW_Abstract | EW_Split
       and then Get_Base_Type (Base_Why_Type (Right)) in EW_Abstract | EW_Split
       and then Fullview_Not_In_SPARK (Get_Ada_Node (+Left))
       and then Fullview_Not_In_SPARK (Get_Ada_Node (+Right)));

   --------------------------
   -- Is_Record_Conversion --
   --------------------------

   function Is_Record_Conversion (Left, Right : W_Type_Id) return Boolean
   is (Get_Base_Type (Base_Why_Type (Left)) in EW_Abstract | EW_Split and then
       Get_Base_Type (Base_Why_Type (Right)) in EW_Abstract | EW_Split and then
       Has_Record_Type (Get_Ada_Node (+Left)) and then
       Has_Record_Type (Get_Ada_Node (+Right)));

   ---------
   -- LCA --
   ---------

   function LCA
     (Left  : W_Type_Id;
      Right : W_Type_Id;
      Force : Boolean := False) return W_Type_Id
   is
      Left_Base, Right_Base : EW_Type;

   begin
      if not Force and then Eq_Base (Left, Right) then
         return Left;

      else
         Left_Base := Get_Base_Type (Base_Why_Type (Left));
         Right_Base := Get_Base_Type (Base_Why_Type (Right));

         if Left_Base = EW_Abstract and then Right_Base = EW_Abstract then
            declare
               L : constant Node_Id := Get_Ada_Node (+Left);
               R : constant Node_Id := Get_Ada_Node (+Right);
            begin
               pragma Assert
                 (Root_Record_Type (L) = Root_Record_Type (R));
               return EW_Abstract (Root_Record_Type (L));
            end;

         else
            return Why_Types (Type_Hierarchy.LCA (Left_Base, Right_Base));
         end if;
      end if;
   end LCA;

   -------------------------
   -- Loop_Exception_Name --
   -------------------------

   function Loop_Exception_Name
     (E     : Entity_Id;
      Local : Boolean := False)
      return W_Name_Id
   is
      Suffix : constant Name_Id :=
        NID (Capitalize_First (Short_Name (E)));
   begin
      if Local then
         return New_Name (Ada_Node => E, Symbol => Suffix);
      else
         return
           New_Name
             (Ada_Node => E,
              Symbol   => Suffix,
              Module   => E_Module (E));
      end if;
   end Loop_Exception_Name;

   ----------------------------
   -- New_Abstract_Base_Type --
   ----------------------------

   function New_Abstract_Base_Type (E : Entity_Id) return W_Type_Id is
   begin
      return New_Kind_Base_Type (E, EW_Abstract);
   end New_Abstract_Base_Type;

   ------------------------
   -- New_Kind_Base_Type --
   ------------------------

   function New_Kind_Base_Type
     (E    : Entity_Id;
      Kind : EW_Type) return W_Type_Id is
   begin
      if Kind = EW_Abstract then
         return New_Type (Ada_Node   => E,
                          Is_Mutable => False,
                          Base_Type  => EW_Abstract,
                          Name       => To_Why_Type (E));
      else
         return New_Type (Ada_Node   => E,
                          Is_Mutable => False,
                          Base_Type  => EW_Split,
                          Name       =>
                            New_Name
                              (Ada_Node => E,
                               Symbol   => NID ("__split"),
                               Module   => E_Module (E)));
      end if;
   end New_Kind_Base_Type;

   --------------------
   -- New_Named_Type --
   --------------------

   function New_Named_Type (Name : W_Name_Id) return W_Type_Id is
   begin
      return New_Type (Ada_Node   => Empty,
                       Is_Mutable => False,
                       Base_Type  => EW_Abstract,
                       Name       => Name);
   end New_Named_Type;

   function New_Named_Type (S : String) return W_Type_Id is
   begin
      return New_Named_Type (Name => New_Name (Symbol => NID (S)));
   end New_Named_Type;

   ------------------
   -- New_Ref_Type --
   ------------------

   function New_Ref_Type (Ty : W_Type_Id) return W_Type_Id is
   begin
      if Get_Is_Mutable (+Ty) then
         return Ty;
      else
         return
           New_Type (Ada_Node   => Get_Ada_Node (+Ty),
                     Base_Type  => Get_Base_Type (+Ty),
                     Name       => Get_Name (+Ty),
                     Is_Mutable => True);
      end if;
   end New_Ref_Type;

   -----------------
   -- Open_Theory --
   -----------------

   procedure Open_Theory (P       : in out Why_Section;
                          Module  : W_Module_Id;
                          Comment : String)
   is
      S : constant String :=
        Capitalize_First (Get_Name_String (Get_Name (Module)));
   begin
      P.Cur_Theory :=
        New_Theory_Declaration (Name    => NID (S),
                                Kind    => EW_Module,
                                Comment => NID (Comment));
   end Open_Theory;

   ---------------
   -- To_Why_Id --
   ---------------

   function To_Why_Id
     (E        : Entity_Id;
      Domain   : EW_Domain := EW_Prog;
      Local    : Boolean := False;
      Dispatch : Boolean := False;
      Rec      : Entity_Id := Empty;
      Typ      : W_Type_Id := Why_Empty) return W_Identifier_Id
   is
      Suffix : constant String :=
        (if Ekind (E) in Subprogram_Kind
                       | E_Subprogram_Body
                       | Named_Kind
                       | Type_Kind
                       | Object_Kind
                       | E_Abstract_State
         then
            Short_Name (E)
         else "");
   begin
      --  The component case is sufficiently different to treat it
      --  independently

      if Ekind (E) in E_Component | E_Discriminant then
         declare
            Field : constant String :=
              To_String (WNE_Rec_Comp_Prefix) & Get_Name_String (Chars (E));
            Ada_N : constant Node_Id :=
              (if Rec = Empty then
                  Unique_Entity (Scope (E)) else Rec);
            Module : constant W_Module_Id :=
              E_Module (if Rec = Empty and Ekind (E) = E_Discriminant then
                             Unique_Entity (Root_Record_Type (Ada_N))
                        else Ada_N);
         begin
            if Local then
               return New_Identifier (Ada_Node => Ada_N,
                                      Name     => Field,
                                      Typ      => Typ);
            else
               return
                 New_Identifier
                   (Ada_Node => Ada_N,
                    Name     => Field,
                    Module   => Module,
                    Typ      => Typ);
            end if;
         end;

      elsif Local then
         return New_Identifier (Ada_Node => E, Name => Suffix, Typ => Typ);

      elsif Suffix = "" then
         return New_Identifier (Ada_Node => E,
                                Name     => Full_Name (E),
                                Typ      => Typ);

      else
         declare
            Module : constant W_Module_Id :=
              (if Ekind (E) in Subprogram_Kind and then Domain = EW_Prog then
                 E_Axiom_Module (E)
               else
                 E_Module (E));
            Namespace : constant Name_Id :=
              (if Dispatch then
                 NID (To_String (WNE_Dispatch_Module))
               else
                  No_Name);
         begin
            return
              New_Identifier
                (Ada_Node  => E,
                 Name      => Suffix,
                 Namespace => Namespace,
                 Module    => Module,
                 Typ       => Typ);
         end;
      end if;
   end To_Why_Id;

   function To_Why_Id (Obj : String; Local : Boolean) return W_Identifier_Id
   is
   begin
      if Obj = SPARK_Xrefs.Name_Of_Heap_Variable then
         return New_Identifier (Name => SPARK_Xrefs.Name_Of_Heap_Variable);
      else
         declare
            Name : constant String :=
              Avoid_Why3_Keyword (Extract_Object_Name (Obj));
         begin
            if Local then
               return New_Identifier (Name => Name);
            else
               return Prefix (New_Module (File => No_Name, Name => NID (Obj)),
                              Name);
            end if;
         end;
      end if;
   end To_Why_Id;

   -----------------
   -- To_Why_Type --
   -----------------

   function To_Why_Type
     (E     : Entity_Id;
      Local : Boolean := False) return W_Name_Id
   is
      Suffix : constant String := Short_Name (E);
   begin
      --  Classwide types are translated as their corresponding specific tagged
      --  types.

      if Ekind (E) in E_Class_Wide_Type | E_Class_Wide_Subtype then
         return To_Why_Type (Corresponding_Tagged (E), Local);

      elsif Local then
         return New_Name (Ada_Node => E, Symbol => NID (Suffix));

      else
         return
           New_Name
             (Ada_Node => E,
              Symbol   => NID (Suffix),
              Module   => E_Module (E));
      end if;

   end To_Why_Type;

   function To_Why_Type (T : String) return W_Type_Id is
   begin
      if T = SPARK_Xrefs.Name_Of_Heap_Variable then
         return Type_Of_Heap;
      else
         return EW_Private_Type;
      end if;
   end To_Why_Type;

   ------------------
   -- Type_Of_Node --
   ------------------

   function Type_Of_Node (N : Node_Id) return W_Type_Id
   is
      E : constant Entity_Id := Type_Of_Node (N);
   begin

      --  Handle special cases boolean/real

      if Is_Standard_Boolean_Type (E) then
         return EW_Bool_Type;
      elsif E = Universal_Fixed then
         return EW_Real_Type;

      --  look through 'old and 'loop_entry

      elsif Nkind (N) = N_Attribute_Reference
        and then Get_Attribute_Id (Attribute_Name (N)) in
          Attribute_Old | Attribute_Loop_Entry
      then
         return Type_Of_Node (Prefix (N));

      --  for objects, we want to look at the Why type of the Why object

      elsif Nkind (N) in N_Identifier | N_Expanded_Name
        and then Ekind (Entity (N)) in Object_Kind
        and then Ekind (Entity (N)) not in E_Discriminant | E_Component
      then
         return Why_Type_Of_Entity (Entity (N));
      else
         return EW_Abstract (E);
      end if;
   end Type_Of_Node;

   --------
   -- Up --
   --------

   function Up (WT : W_Type_Id) return W_Type_Id is
      Kind : constant EW_Type := Get_Base_Type (WT);
   begin
      case Kind is
         when EW_Abstract =>
            return Base_Why_Type (WT);
         when others =>
            return Why_Types (Type_Hierarchy.Up (Kind));
      end case;
   end Up;

   --------
   -- Up --
   --------

   function Up (From, To : W_Type_Id) return W_Type_Id is
   begin
      if Eq_Base (From, To) then
         return From;
      else
         return Up (From);
      end if;
   end Up;

begin
   Type_Hierarchy.Move_Child (EW_Unit, EW_Real);
   Type_Hierarchy.Move_Child (EW_Int, EW_Bool);
   Type_Hierarchy.Move_Child (EW_Real, EW_Int);
   Type_Hierarchy.Freeze;
end Why.Inter;
