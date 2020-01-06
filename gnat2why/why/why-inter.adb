------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             W H Y - I N T E R                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2020, AdaCore                     --
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

with Ada.Containers.Hashed_Maps;
with Flow_Generated_Globals.Phase_2;
with Flow_Utility;
with Flow_Types;                 use Flow_Types;
with Gnat2Why.Tables;            use Gnat2Why.Tables;
with Snames;                     use Snames;
with SPARK_Definition;           use SPARK_Definition;
with SPARK_Frame_Conditions;     use SPARK_Frame_Conditions;
with SPARK_Util;                 use SPARK_Util;
with SPARK_Util.External_Axioms; use SPARK_Util.External_Axioms;
with SPARK_Xrefs;                use SPARK_Xrefs;
with Stand;                      use Stand;
with String_Utils;               use String_Utils;
with Uintp;
with Why.Atree.Accessors;        use Why.Atree.Accessors;
with Why.Atree.Builders;         use Why.Atree.Builders;
with Why.Atree.Modules;          use Why.Atree.Modules;
with Why.Atree.Mutators;         use Why.Atree.Mutators;
with Why.Atree.Traversal;        use Why.Atree.Traversal;
with Why.Conversions;            use Why.Conversions;
with Why.Gen.Arrays;             use Why.Gen.Arrays;
with Why.Gen.Expr;               use Why.Gen.Expr;
with Why.Gen.Names;              use Why.Gen.Names;
with Why.Gen.Pointers;           use Why.Gen.Pointers;
with Why.Gen.Scalars;            use Why.Gen.Scalars;
with Why.Images;                 use Why.Images;

---------------
-- Why.Inter --
---------------

package body Why.Inter is

   package Symbol_To_Theory_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Symbol,
      Element_Type    => W_Theory_Declaration_Id,
      Hash            => GNATCOLL.Symbols.Hash,
      Equivalent_Keys => "=");

   Symbol_To_Theory_Map : Symbol_To_Theory_Maps.Map;

   -----------------------
   -- Local Subprograms --
   -----------------------

   subtype N_Has_Theory is Node_Kind with
     Static_Predicate => N_Has_Theory in N_String_Literal |
                                         N_Aggregate;
   --  Subtype of nodes (instead of entities) which have an associated theory,
   --  and should be treated specially.

   function Extract_Object_Name (Obj : String) return String;
   --  Extract the name after the last "__"; return Obj when the string does
   --  not contain "__". This is useful to determine the user name of an Ada
   --  entity when all we have is its fully scoped name (for hidden effects of
   --  other units).

   function Compute_Ada_Node_Set (S : Why_Node_Sets.Set) return Node_Sets.Set;
   --  Transform a module set into a node set by taking the Ada_Node of each
   --  element.

   function LCA (Left, Right : W_Type_Id) return W_Type_Id;
   --  Return the lowest common ancestor in base type hierarchy,
   --  i.e. the smallest base type B such that Left <= B and Right <= B.
   --  If Force = True, we also force B to be different from Left or Right,
   --  even in the case Left = Right.

   function EW_Abstract_Shared
     (N    : Node_Id;
      Kind : EW_Type) return W_Type_Id
     with Pre => Is_Type (N)
                 and then Kind in EW_Abstract | EW_Split;
   --  Build a type node from an Ada type node, either of kind Split or
   --  Abstract.

   function New_Kind_Base_Type (E : Entity_Id; Kind : EW_Type) return W_Type_Id
     with Pre => Kind in EW_Abstract | EW_Split;
   --  @param E The type entity for which we want to construct a why type
   --  @param Kind The kind we want the Why type to have. For now, EW_Split is
   --              only supported for arrays and discrete types.
   --  @return The why type to be used for E. It will have the kind Kind. Its
   --          name may be the same as another type's name to avoid name
   --          duplication. It is the case for split forms and static array
   --          types.

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

      procedure Integer_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Integer_Constant_Id);

      procedure Modular_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Modular_Constant_Id);

      procedure Real_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Real_Constant_Id);

      procedure Fixed_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Fixed_Constant_Id);

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

      -----------------------
      -- Identifier_Pre_Op --
      -----------------------

      procedure Identifier_Pre_Op
        (State : in out Search_State;
         Node  : W_Identifier_Id)
      is
      begin
         --  ??? special hack to be removed at some point

         if Node = Int_Unary_Minus then
            State.S.Include (+Int_Module);
         end if;

         --  ??? Little optimization that also works around a bug
         --  We only need to traverse the name node, type node is not required
         --  because the module for the name will already point to the module
         --  for the type. This also avoids cases where apparently the type
         --  node points to some module which should not be used

         Traverse (State, +Get_Name (Node));
         State.Control := Abandon_Children;
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

      -----------------------------
      -- Modular_Constant_Pre_Op --
      -----------------------------

      procedure Modular_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Modular_Constant_Id) is
         Typ : constant W_Type_Id := Get_Typ (Node);
         pragma Unreferenced (Node);
      begin
         if Typ = EW_BitVector_8_Type then
            State.S.Include (+M_BVs (BV8).Module);
         elsif Typ = EW_BitVector_16_Type then
            State.S.Include (+M_BVs (BV16).Module);
         elsif Typ = EW_BitVector_32_Type then
            State.S.Include (+M_BVs (BV32).Module);
         elsif Typ = EW_BitVector_64_Type then
            State.S.Include (+M_BVs (BV64).Module);
         else
            raise Unexpected_Node;
         end if;
      end Modular_Constant_Pre_Op;

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

      SS : Search_State := (Control => Continue, S => Empty_Set);

   --  Start of processing for Compute_Ada_Nodeset

   begin
      Traverse (SS, +W);
      return SS.S;
   end Compute_Module_Set;

   ------------------------
   -- Add_Use_For_Entity --
   ------------------------

   procedure Add_Use_For_Entity
     (P               : W_Section_Id;
      E               : Entity_Id;
      Use_Kind        : EW_Clone_Type := EW_Clone_Default;
      With_Completion : Boolean := True)
   is
      Module : constant W_Module_Id := E_Module (E);

   begin
      --  In the few special cases for which the Full_Name of N is not based on
      --  its Unique_Name, the corresponding theories are standard ones (dealt
      --  with separately). Return in that case, to avoid generating wrong
      --  includes based on a non-unique Full_Name.

      if Full_Name_Is_Not_Unique_Name (E) then
         return;
      end if;

      Add_With_Clause (P, Module, Use_Kind);

      if With_Completion
        and then (not Entity_In_Ext_Axioms (E) or else Is_Type (E))
      then
         Add_With_Clause (P, E_Axiom_Module (E), Use_Kind);
      end if;
   end Add_Use_For_Entity;

   ---------------------
   -- Add_With_Clause --
   ---------------------

   procedure Add_With_Clause (T        : W_Theory_Declaration_Id;
                              Module   : W_Module_Id;
                              Use_Kind : EW_Clone_Type;
                              Th_Type  : EW_Theory_Type := EW_Module)
   is
      Use_Kind2 : constant EW_Clone_Type :=
        (if Module in Int_Module | RealInfix
         then EW_Import
         else Use_Kind);
      --  ??? override the Use_Kind given by the caller

   begin
      Theory_Declaration_Append_To_Includes
        (T,
         New_Include_Declaration
           (Module   => Module,
            Use_Kind => Use_Kind2,
            Kind     => Th_Type));
   end Add_With_Clause;

   procedure Add_With_Clause (P        : W_Section_Id;
                              Module   : W_Module_Id;
                              Use_Kind : EW_Clone_Type;
                              Th_Type  : EW_Theory_Type := EW_Module) is
   begin
      Add_With_Clause (Why_Sections (P).Cur_Theory, Module, Use_Kind, Th_Type);
   end Add_With_Clause;

   -------------------
   -- Base_Why_Type --
   -------------------

   function Base_Why_Type (W : W_Type_Id) return W_Type_Id is
      Kind : constant EW_Type := Get_Type_Kind (W);
   begin
      case Kind is
         when EW_Abstract
            | EW_Split
            | EW_Wrapper
         =>
            return Base_Why_Type (Get_Ada_Node (+W));

         when others =>
            return W;
      end case;
   end Base_Why_Type;

   function Base_Why_Type (N : Node_Id) return W_Type_Id is

      E   : constant W_Type_Id := Get_EW_Term_Type (N);
      Typ : Entity_Id :=
        (if Nkind (N) in N_Entity and then Is_Type (N) then N
         else Etype (N));
   begin
      if E = Why_Empty then

         --  For record or private types, go through subtypes to get the base
         --  type.
         --  For pointers, get the type of the root type (pointers may share
         --  same representative theory while one is not the subtype of the
         --  other, exp: named and anonymous types of the same designated
         --  type).

         loop
            Typ := Retysp (Typ);

            if (Is_Record_Type (Typ) or else Is_Private_Type (Typ))
              and then Ekind (Typ) in SPARK_Util.Types.Subtype_Kind
            then
               Typ := Etype (Typ);
            elsif Is_Access_Type (Typ) then
               return EW_Abstract (Root_Pointer_Type (Typ));
            else
               return EW_Abstract (Typ);
            end if;
         end loop;
      else
         return E;
      end if;
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

   ---------------------------
   -- Base_Why_Type_No_Bool --
   ---------------------------

   function Base_Why_Type_No_Bool (N : Node_Id) return W_Type_Id is
      E : constant W_Type_Id := Base_Why_Type (N);
   begin
      if E = EW_Bool_Type then
         return EW_Int_Type;
      else
         return E;
      end if;
   end Base_Why_Type_No_Bool;

   function Base_Why_Type_No_Bool (Typ : W_Type_Id) return W_Type_Id is
      Kind : constant W_Type_Id := Base_Why_Type (Typ);
   begin
      if Kind = EW_Bool_Type then
         return EW_Int_Type;
      else
         return Kind;
      end if;
   end Base_Why_Type_No_Bool;

   function Base_Why_Type_No_Bool (Expr : W_Expr_Id) return W_Type_Id is
      (Base_Why_Type_No_Bool (Get_Type (Expr)));

   ------------------
   -- Close_Theory --
   ------------------

   procedure Close_Theory
     (P              : W_Section_Id;
      Kind           : Theory_Kind;
      Defined_Entity : Entity_Id := Empty)
   is
      S : constant Why_Node_Sets.Set :=
        Compute_Module_Set (+(Why_Sections (P).Cur_Theory));

      function Is_Relevant_For_Imports
        (N : Node_Or_Entity_Id)
         return Boolean
      with Pre => (if Present (N)
                   then (if Nkind (N) in N_Entity
                         then Ekind (N) /= E_Void
                           and then
                             (if Is_Full_View (N)
                              then Present (Partial_View (N)))
                           and then
                             (if Ekind (N) = E_Loop_Parameter
                              then not Is_Quantified_Loop_Param (N))
                         else Nkind (N) = N_Aggregate
                           and then Is_Array_Type (Etype (N))));
      --  Returns True if N is relevant for theory imports
      --
      --  We need to consider entities and some non-entities such as string
      --  literals. We do *not* consider its Full_View. Loop parameters are a
      --  bit special, we want to deal with them only if they are from loop,
      --  but not from a quantifier.

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
         use Flow_Generated_Globals.Phase_2;
      begin
         for N of S loop
            if Nkind (N) not in N_Entity
              or else not Entity_In_Ext_Axioms (N)
            then
               Add_With_Clause (P,
                                E_Axiom_Module (N),
                                EW_Clone_Default);

               --  Add a with clause for the theory containing the post axiom
               --  of a recursive function. We do not include it when proving
               --  the subprogram itself or mutually recursive subprograms as
               --  it would be unsound. We do not include it either when
               --  proving a package elaboration, or VCs for a type declaration
               --  as it is not clear yet how we can decide whether those are
               --  mutually recursive with a function or not.

               if Present (Defined_Entity)
                 and then Is_Subprogram_Or_Entry (Defined_Entity)
                 and then Nkind (N) in N_Entity
                 and then Is_Subprogram_Or_Entry (N)
                 and then Is_Recursive (N)
                 and then Has_Post_Axiom (N)
                 and then not Mutually_Recursive (Defined_Entity, N)
               then
                  Add_With_Clause (P,
                                   E_Rec_Axiom_Module (N),
                                   EW_Clone_Default);
               end if;
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

      -----------------------------
      -- Is_Relevant_For_Imports --
      -----------------------------

      function Is_Relevant_For_Imports
        (N : Node_Or_Entity_Id)
         return Boolean
         renames Present;

      -------------------------
      -- Record_Dependencies --
      -------------------------

      procedure Record_Dependencies (Defined_Entity : Entity_Id) is
      begin
         for M of S loop
            declare
               Ada_Node : constant Node_Id := Get_Ada_Node (M);

            begin
               if Is_Relevant_For_Imports (Ada_Node) then
                  Add_To_Graph (Entity_Dependencies,
                                Defined_Entity,
                                Ada_Node);
               end if;
            end;
         end loop;
      end Record_Dependencies;

   --  Start of processing for Close_Theory

   begin
      Add_With_Clause (P, M_Main.Module, EW_Import);
      Add_With_Clause (P, Int_Module, EW_Import);

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
            Add_Axiom_Imports
              (Get_Graph_Closure (Map  => Entity_Dependencies,
                                  From => Compute_Ada_Node_Set (S)));
      end case;

      declare
         Th : constant W_Theory_Declaration_Id := Why_Sections (P).Cur_Theory;
         N  : constant Symbol := Get_Name (Th);
      begin
         Why_Sections (P).Theories.Append (+Th);
         Symbol_To_Theory_Map.Insert (N, Th);
      end;
      Why_Sections (P).Cur_Theory := Why_Empty;
   end Close_Theory;

   ---------------------
   -- Dispatch_Entity --
   ---------------------

   function Dispatch_Entity (E : Entity_Id) return W_Section_Id is
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

         when Entry_Kind
            | E_Procedure
         =>
            return WF_Context;

         --  Functions without read/write global effects are declared in the
         --  "type" Why files instead of the "context" Why files, so that they
         --  can be used as parameters of generics whose axiomatization in Why
         --  is written manually (example: formal containers).

         when E_Function =>
            return
              (if Flow_Utility.Has_Proof_Globals (E)
               then WF_Context
               else WF_Pure);

         when Object_Kind =>

            --  Constants are defined in type files. Their defining axiom, if
            --  any, is defined as a completion in the type or context file.

            if not Is_Mutable_In_Why (E) then
               return WF_Pure;

            elsif Ekind (E) = E_Discriminant
              and then Is_Ext_Axioms_Discriminant (E)
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

         when others =>
            raise Program_Error;
      end case;
   end Dispatch_Entity;

   --------------------------------
   -- Dispatch_Entity_Completion --
   --------------------------------

   function Dispatch_Entity_Completion (E : Entity_Id)
                                        return W_Section_Id is
   begin

      --  Completion modules of types are only used by VC generation modules
      --  and completion modules of subprograms. Other completion modules are
      --  only used by VC generation modules.
      --  Since they are generated after defining modules and before VC
      --  generation modules, the completions of types will have all the
      --  required definitions and they will be available when necessary.

      if Nkind (E) in N_Entity and then Is_Type (E) then
         return WF_Context;
      else
         return WF_Axioms;
      end if;
   end Dispatch_Entity_Completion;

   -------------
   -- Eq_Base --
   -------------

   function Eq_Base (Left, Right : W_Type_Id) return Boolean is
   begin
      if Left = Right then
         return True;

      --  Builtin nodes can be compared directly

      elsif Get_Type_Kind (Left) in EW_Builtin | EW_Wrapper then
         return False;

      --  Two types with different kinds cannot be equal

      elsif Get_Type_Kind (Left) /= Get_Type_Kind (Right) then
         return False;

      --  For EW_Abstract and EW_Split types, compare the ada node

      elsif Get_Type_Kind (Left) in EW_Abstract | EW_Split then

         --  Dummy EW_Abstract types are introduced for record private parts.
         --  Eq_Base should only be called on such types if they are equal.

         pragma Assert
           ((No (Get_Ada_Node (+Left))
            and then No (Get_Ada_Node (+Right))
            and then Get_Name (+Left) = Get_Name (+Right))
            or else (Present (Get_Ada_Node (+Left))
              and then Present (Get_Ada_Node (+Right))));

         return Get_Ada_Node (+Left) = Get_Ada_Node (+Right);
      else
         raise Program_Error;
      end if;
   end Eq_Base;

   ---------------
   -- Eq_In_Why --
   ---------------

   function Eq_In_Why (Left, Right : W_Type_Id) return Boolean is
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
               return Get_Symb (N1) = Get_Symb (N2);
            else
               return False;
            end if;
         end;
      end;
   end Eq_In_Why;

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

      elsif Is_Class_Wide_Type (N) then
         return EW_Abstract_Shared (Specific_Tagged (N), Kind);

      elsif Retysp (N) /= N then
         return EW_Abstract_Shared (Retysp (N), Kind);
      else
         pragma Assert (Entity_In_SPARK (N));
         return New_Kind_Base_Type (N, Kind);
      end if;
   end EW_Abstract_Shared;

   -------------------
   -- EW_Fixed_Type --
   -------------------

   function EW_Fixed_Type (E : Entity_Id) return W_Type_Id is
      (Get_Fixed_Point_Theory (E).T);

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

   ---------------
   -- Find_Decl --
   ---------------

   function Find_Decl (S : Symbol) return W_Theory_Declaration_Id is
   begin
      return Symbol_To_Theory_Map.Element (S);
   end Find_Decl;

   -----------------
   -- Get_EW_Type --
   -----------------

   function Get_EW_Type (T : Node_Id) return EW_Type is
      E : constant W_Type_Id := Get_EW_Term_Type (T);
   begin
      if E = Why_Empty then
         return EW_Abstract;
      else
         return Get_Type_Kind (E);
      end if;
   end Get_EW_Type;

   ----------------------
   -- Get_EW_Term_Type --
   ----------------------

   function Get_EW_Term_Type (N : Node_Id) return W_Type_Id is
      Ty : Node_Id := N;
   begin
      if Nkind (N) /= N_Defining_Identifier or else not (Is_Type (N)) then
         Ty := Etype (N);
      end if;

      case Ekind (Ty) is
         when Fixed_Point_Kind =>
            return EW_Fixed_Type (Ty);

         when Float_Kind =>
            if Is_Single_Precision_Floating_Point_Type (Etype (Ty)) then
               return EW_Float_32_Type;
            elsif Is_Double_Precision_Floating_Point_Type (Etype (Ty)) then
               return EW_Float_64_Type;
            else
               raise Program_Error;
            end if;

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
               return EW_Bool_Type;
            elsif Ty = Universal_Fixed then
               return EW_Real_Type;
            elsif Is_Modular_Integer_Type (Ty) then
               declare
                  Size : Uintp.Uint;
               begin
                  Size := Modular_Size (Ty);

                  if Uintp.UI_Le (Size, 8) then
                     return EW_BitVector_8_Type;
                  elsif Uintp.UI_Le (Size, 16) then
                     return EW_BitVector_16_Type;
                  elsif Uintp.UI_Le (Size, 32) then
                     return EW_BitVector_32_Type;
                  elsif Uintp.UI_Le (Size, 64) then
                     return EW_BitVector_64_Type;
                  else
                     return EW_Int_Type;
                  end if;
               end;
            else
               return EW_Int_Type;
            end if;

         when Private_Kind =>
            if Full_View_Not_In_SPARK (Ty) then
               return Why_Empty;
            else
               return Get_EW_Term_Type (Retysp (Ty));
            end if;

         when others =>
            return Why_Empty;
      end case;
   end Get_EW_Term_Type;

   -------------------------
   -- Goto_Exception_Name --
   -------------------------

   function Goto_Exception_Name (E : Entity_Id) return W_Name_Id is
      Suffix : constant Symbol :=
        NID (Capitalize_First (Short_Name (E)) & "__goto");
   begin
      return New_Name (Ada_Node => E, Symb => Suffix);
   end Goto_Exception_Name;

   -------------------------
   -- Is_Array_Conversion --
   -------------------------

   function Is_Array_Conversion (Left, Right : W_Type_Id) return Boolean
   is (Get_Type_Kind (Base_Why_Type (Left)) in EW_Abstract | EW_Split and then
       Get_Type_Kind (Base_Why_Type (Right)) in EW_Abstract | EW_Split and then
       Has_Array_Type (Get_Ada_Node (+Left)) and then
       Has_Array_Type (Get_Ada_Node (+Right)));

   ---------------------------
   -- Is_Pointer_Conversion --
   ---------------------------

   function Is_Pointer_Conversion (Left, Right : W_Type_Id) return Boolean
   is (Get_Type_Kind (Base_Why_Type (Left)) in EW_Abstract | EW_Split and then
       Get_Type_Kind (Base_Why_Type (Right)) in EW_Abstract | EW_Split and then
       Has_Access_Type (Get_Ada_Node (+Left)) and then
       Has_Access_Type (Get_Ada_Node (+Right)));

   ---------------------------
   -- Is_Private_Conversion --
   ---------------------------

   function Is_Private_Conversion (Left, Right : W_Type_Id) return Boolean
   is (Get_Type_Kind (Base_Why_Type (Left)) in EW_Abstract | EW_Split
       and then Get_Type_Kind (Base_Why_Type (Right)) in EW_Abstract | EW_Split
       and then Full_View_Not_In_SPARK (Get_Ada_Node (+Left))
       and then Full_View_Not_In_SPARK (Get_Ada_Node (+Right)));

   --------------------------
   -- Is_Record_Conversion --
   --------------------------

   function Is_Record_Conversion (Left, Right : W_Type_Id) return Boolean
   is (Get_Type_Kind (Base_Why_Type (Left)) in EW_Abstract | EW_Split and then
       Get_Type_Kind (Base_Why_Type (Right)) in EW_Abstract | EW_Split and then
       Has_Record_Type (Get_Ada_Node (+Left)) and then
       Has_Record_Type (Get_Ada_Node (+Right)));

   ---------------------
   -- Need_Conversion --
   ---------------------

   function Need_Conversion (Expr : W_Expr_Id) return Boolean is
   begin
      if Get_Kind (+Expr) = W_Identifier then
         declare
            Expr2 : constant W_Identifier_Id := W_Identifier_Id (Expr);
            Name  : constant W_Name_Id := Get_Name (Expr2);
         begin
            return Img (Get_Symb (Name)) /= To_String (WNE_Null_Pointer);
         end;

      else
         return True;
      end if;
   end Need_Conversion;

   ---------
   -- LCA --
   ---------

   function LCA
     (Left  : W_Type_Id;
      Right : W_Type_Id) return W_Type_Id
   is
      Left_Base, Right_Base : W_Type_Id;

   begin
      if Eq_Base (Left, Right) then
         return Left;
      end if;

      Left_Base := Base_Why_Type (Left);
      Right_Base := Base_Why_Type (Right);

      if (Left_Base = EW_Int_Type and then Right = EW_Bool_Type)
        or else
          (Left_Base = EW_Bool_Type and then Right_Base = EW_Int_Type)
      then
         return EW_Int_Type;
      elsif Left_Base = EW_BitVector_8_Type or else
        Right_Base = EW_BitVector_8_Type
      then
         return EW_BitVector_8_Type;
      elsif Left_Base = EW_BitVector_16_Type or else
        Right_Base = EW_BitVector_16_Type
      then
         return EW_BitVector_16_Type;
      elsif Left_Base = EW_BitVector_32_Type or else
        Right_Base = EW_BitVector_32_Type
      then
         return EW_BitVector_32_Type;
      elsif Left_Base = EW_BitVector_64_Type or else
        Right_Base = EW_BitVector_64_Type
      then
         return EW_BitVector_64_Type;
      end if;

      --  There are no other uses of this subprogram for now

      raise Program_Error;
   end LCA;

   -------------------------
   -- Loop_Exception_Name --
   -------------------------

   function Loop_Exception_Name
     (E     : Entity_Id;
      Local : Boolean := False)
      return W_Name_Id
   is
      Suffix : constant Symbol :=
        NID (Capitalize_First (Short_Name (E)));
   begin
      if Local then
         return New_Name (Ada_Node => E, Symb => Suffix);
      else
         return
           New_Name
             (Ada_Node => E,
              Symb     => Suffix,
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

      --  We avoid having renaming of types in Why to allow using the same
      --  reference type.

      if Is_Static_Array_Type (Retysp (E))
        or else (Kind = EW_Split and then Has_Array_Type (E))
      then

         --  Static array types and arrays split forms are in fact Why3 maps

         return New_Type
           (Ada_Node   => E,
            Is_Mutable => False,
            Type_Kind  => Kind,
            Name       =>
              New_Name
                (Ada_Node => E,
                 Symb     => NID ("map"),
                 Module   =>
                   New_Module
                     (File => No_Symbol,
                      Name => Img (Get_Array_Theory_Name (E)))));
      elsif Kind = EW_Split and then Has_Fixed_Point_Type (E) then

         --  The base type of a fixed point type is __fixed. Do not call
         --  Base_Why_Type which may fail if the theory for the small value of
         --  E has not been constructed yet.

         return New_Type
           (Ada_Node   => E,
            Is_Mutable => False,
            Type_Kind  => Kind,
            Name       => Get_Name (M_Main.Fixed_Type));
      elsif Kind = EW_Split then

         --  Discrete types split forms are their base why type

         pragma Assert (Use_Split_Form_For_Type (E));
         return New_Type
           (Ada_Node   => E,
            Is_Mutable => False,
            Type_Kind  => EW_Split,
            Name       => Get_Name (Base_Why_Type (E)));
      else
         return New_Type (Ada_Node   => E,
                          Is_Mutable => False,
                          Type_Kind  => EW_Abstract,
                          Name       => To_Why_Type (E));
      end if;
   end New_Kind_Base_Type;

   --------------------
   -- New_Named_Type --
   --------------------

   function New_Named_Type (Name : W_Name_Id) return W_Type_Id is
   begin
      return New_Type (Ada_Node   => Empty,
                       Is_Mutable => False,
                       Type_Kind  => EW_Abstract,
                       Name       => Name);
   end New_Named_Type;

   function New_Named_Type (S : String) return W_Type_Id is
   begin
      return New_Named_Type (Name => New_Name (Symb => NID (S)));
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
                     Type_Kind  => Get_Type_Kind (+Ty),
                     Name       => Get_Name (+Ty),
                     Is_Mutable => True);
      end if;
   end New_Ref_Type;

   -----------------
   -- Open_Theory --
   -----------------

   procedure Open_Theory
     (P       : W_Section_Id;
      Module  : W_Module_Id;
      Comment : String) is
   begin
      Why_Sections (P).Cur_Theory :=
        New_Theory_Declaration (Name    => Get_Name (Module),
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
      Selector : Selection_Kind := Standard;
      No_Comp  : Boolean := False;
      Rec      : Entity_Id := Empty;
      Typ      : W_Type_Id := Why_Empty) return W_Identifier_Id
   is
      Suffix : constant String := Short_Name (E);

   begin
      --  Components names are prefixed by a constant string, and are always
      --  expressed wrt to their record.

      if (Ekind (E) in E_Component | E_Discriminant
          or else Is_Part_Of_Protected_Object (E)
          or else Rec /= Empty)
          and then not No_Comp
      then
         pragma Assert (Rec /= Empty);
         declare
            Ada_N  : constant Entity_Id := Retysp (Rec);
            Module : constant W_Module_Id := E_Module (Ada_N);
            Orig   : constant Entity_Id :=
              (if Ekind (E) in E_Component | E_Discriminant | Type_Kind
               then Representative_Component (E)
               else E);
            Field  : constant String :=
              To_String (WNE_Rec_Comp_Prefix) & (Full_Name (Orig));
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

      else
         declare
            Module : constant W_Module_Id :=
              (if Ekind (E) in Subprogram_Kind | Entry_Kind
                 and then Domain = EW_Prog
               then
                 E_Axiom_Module (E)
               else
                 E_Module (E));
            Namespace : constant Symbol :=
              (case Selector is
                 when Dispatch  => NID (To_String (WNE_Dispatch_Module)),
                 when No_Return => NID (To_String (WNE_No_Return_Module)),
                 when Refine    => NID (To_String (WNE_Refine_Module)),
                 when Standard  => No_Symbol);
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

   function To_Why_Id
     (Obj   : Entity_Name;
      Local : Boolean)
      return W_Identifier_Id
   is
   begin
      if Is_Heap_Variable (Obj) then
         return New_Identifier (Name => SPARK_Xrefs.Name_Of_Heap_Variable,
                                Typ  => M_Main.Type_Of_Heap);
      else
         declare
            Ada_Name : constant String := To_String (Obj);
            Why_Name : constant String :=
              Avoid_Why3_Keyword (Extract_Object_Name (Ada_Name));
         begin
            if Local then
               return New_Identifier (Name => Why_Name,
                                      Typ  => EW_Private_Type);
            else
               return New_Identifier
                 (Module => New_Module (File => No_Symbol,
                                        Name => Ada_Name),
                  Name   => Why_Name,
                  Typ    => EW_Private_Type);
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

      if Is_Class_Wide_Type (E) then
         return To_Why_Type (Specific_Tagged (E), Local);

      elsif Local then
         return New_Name (Ada_Node => E, Symb => NID (Suffix));

      else
         return
           New_Name
             (Ada_Node => E,
              Symb     => NID (Suffix),
              Module   => E_Module (E));
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
        and then Is_Object (Entity (N))
        and then Ekind (Entity (N)) not in E_Discriminant | E_Component
        and then not Is_Part_Of_Protected_Object (Entity (N))
      then
         return Why_Type_Of_Entity (Entity (N));
      elsif Is_Type (E)
        and then Use_Split_Form_For_Type (E)
      then
         return EW_Split (E);
      else
         return EW_Abstract (E);
      end if;
   end Type_Of_Node;

end Why.Inter;
