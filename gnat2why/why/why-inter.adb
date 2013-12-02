------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                             W H Y - I N T E R                            --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2013, AdaCore                   --
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

with Atree;               use Atree;
with Einfo;               use Einfo;
with Namet;               use Namet;
with Sem_Util;            use Sem_Util;
with SPARK_Xrefs;         use SPARK_Xrefs;
with Sinfo;               use Sinfo;
with Snames;              use Snames;
with Stand;               use Stand;
with String_Utils;        use String_Utils;
with Constant_Tree;

with SPARK_Definition;    use SPARK_Definition;
with SPARK_Util;          use SPARK_Util;

with Flow.Utility;

with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Atree.Tables;    use Why.Atree.Tables;
with Why.Atree.Traversal; use Why.Atree.Traversal;
with Why.Conversions;     use Why.Conversions;
with Why.Gen.Names;       use Why.Gen.Names;

with Why.Images;          use Why.Images;

---------------
-- Why.Inter --
---------------

package body Why.Inter is

   type Why_Types_Array_Type is array (EW_Basic_Type) of W_Type_Id;

   Why_Types_Array : Why_Types_Array_Type := (others => Why_Empty);
   --  is initialized as needed in function Why_Types

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Compute_Ada_Nodeset (W : Why_Node_Id) return
     Node_Sets.Set;
   --  For a given Why node, compute the required Ada nodes, from which we can
   --  compute the necessary inclusions on the Why side

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

   function Get_EW_Term_Type (N : Node_Id) return EW_Type;

   function EW_Abstract_Shared
     (N    : Node_Id;
      Kind : EW_Type) return W_Type_Id
     with Pre => Kind in EW_Abstract | EW_Split;
   --  Build an type node from an Ada type node, either of kind Split or
   --  Abstract

   function New_Kind_Base_Type (E : Entity_Id; Kind : EW_Type) return W_Type_Id
     with Pre => Kind in EW_Abstract | EW_Split;

   package Standard_Imports is

      --  This package serves to trigger the necessary imports on the
      --  _gnatprove_standard file.

      type Standard_Imports_Enum is (SI_Integer,
                                     SI_Float,
                                     SI_Boolean,
                                     SI_Array1,
                                     SI_Array2,
                                     SI_Array3,
                                     SI_Array4
                                    );

      Imports : array (Standard_Imports_Enum) of Boolean;
      --  This array records whether a standard import is necessary

      procedure Clear;
      --  Reset the import information

      procedure Set_SI (E : Entity_Id);
      --  Depending on the entity, set a required import

      function To_Module (E : Standard_Imports_Enum) return W_Module_Id;

   end Standard_Imports;

   package body Standard_Imports is

      procedure Set_SI_Internal (E : Entity_Id);
      --  Internal version of Set_SI doing all the work, with protection
      --  against infinite recursion; is called by Set_SI

      SI_Seen : Node_Sets.Set := Node_Sets.Empty_Set;
      --  "Seen"-Set to infinite recursion of Set_SI_Internal

      -----------
      -- Clear --
      -----------

      procedure Clear is
      begin
         for I in Imports'Range loop
            Imports (I) := False;
         end loop;
      end Clear;

      ---------------------
      -- Set_SI_Internal --
      ---------------------

      procedure Set_SI_Internal (E : Entity_Id) is
      begin
         if not (Nkind (E) in N_Entity) then
            Set_SI_Internal (Etype (E));
            return;
         end if;
         declare
            UE : constant Entity_Id := E;  --  ??? remove indirection
         begin
            if SI_Seen.Contains (UE) then
               return;
            end if;
            SI_Seen.Include (UE);
            if Ekind (UE) in Object_Kind and then
              not Entity_In_SPARK (UE)
            then
               return;
            end if;
            if Ekind (UE) in Type_Kind and then not Entity_In_SPARK (UE) then
               return;
            end if;

            --  Only Standard.Boolean is modeled as bool; any other boolean
            --  subtype is modeled as an abstract type to have range checks.

            if Is_Standard_Boolean_Type (UE) then
               Imports (SI_Boolean) := True;
               Imports (SI_Integer) := True;
            else
               case Ekind (UE) is
               when Discrete_Kind | E_Named_Integer =>
                  Imports (SI_Integer) := True;

               when Float_Kind | Fixed_Point_Kind | E_Named_Real =>
                  Imports (SI_Float) := True;

               when Array_Kind =>
                  Imports (SI_Integer) := True;
                  Set_SI_Internal (Component_Type (UE));
                  case Number_Dimensions (UE) is
                  when 1 =>
                     Imports (SI_Array1) := True;
                  when 2 =>
                     Imports (SI_Array2) := True;
                  when 3 =>
                     Imports (SI_Array3) := True;
                  when 4 =>
                     Imports (SI_Array4) := True;
                  when others =>
                     raise Program_Error;
                  end case;

               when Private_Kind =>
                  if Entity_In_SPARK (MUT (UE)) then
                     Set_SI_Internal (MUT (UE));
                  end if;

               when E_Record_Type | E_Record_Subtype =>
                  declare
                     Field            : Node_Id :=
                       First_Component_Or_Discriminant (UE);
                  begin
                     while Present (Field) loop
                        if Ekind (Field) in Object_Kind then
                           Set_SI_Internal (Etype (Field));
                        end if;
                        Next_Component_Or_Discriminant (Field);
                     end loop;
                  end;

               when Object_Kind =>
                  Set_SI (Etype (UE));

               when Subprogram_Kind =>
                  declare
                     Formal : Node_Id :=
                       First_Formal (UE);
                  begin
                     while Present (Formal) loop
                        Set_SI_Internal (Etype (Formal));
                        Next_Formal (Formal);
                     end loop;
                  end;

               when E_Loop =>
                  null;

               when others =>
                  raise Program_Error;
               end case;
            end if;
         end;
      end Set_SI_Internal;

      ------------
      -- Set_SI --
      ------------

      procedure Set_SI (E : Entity_Id) is
      begin
         Set_SI_Internal (E);
         SI_Seen.Clear;
      end Set_SI;

      ---------------
      -- To_String --
      ---------------

      function To_Module (E : Standard_Imports_Enum) return W_Module_Id is
      begin
         case E is
            when SI_Integer => return Integer_Module;
            when SI_Float   => return Floating_Module;
            when SI_Boolean => return Boolean_Module;
            when SI_Array1  => return Array_Modules (1);
            when SI_Array2  => return Array_Modules (2);
            when SI_Array3  => return Array_Modules (3);
            when SI_Array4  => return Array_Modules (4);
         end case;
      end To_Module;

   end Standard_Imports;

   -------------------------
   -- Compute_Ada_Nodeset --
   -------------------------

   function Compute_Ada_Nodeset (W : Why_Node_Id) return Node_Sets.Set is
      use Node_Sets;

      type Search_State is new Traversal_State with record
         S : Set;
      end record;

      procedure Type_Pre_Op
        (State : in out Search_State;
         Node  : W_Type_Id);

      procedure Identifier_Pre_Op
        (State : in out Search_State;
         Node  : W_Identifier_Id);

      procedure Integer_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Integer_Constant_Id);
      --  Integer constants may require the use of integer infix + or -

      procedure Literal_Pre_Op
        (State : in out Search_State;
         Node  : W_Literal_Id);

      procedure Real_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Real_Constant_Id);
      --  Real constants may require the use of real infix + or -

      procedure Analyze_Ada_Node (S : in out Set; A : Node_Id);
      --  Include if necessary node A or a node derived from A to the set S

      ----------------------
      -- Analyze_Ada_Node --
      ----------------------

      procedure Analyze_Ada_Node (S : in out Set; A : Node_Id) is
         N : Node_Id := Empty;
      begin
         if Present (A) then
            case Nkind (A) is
               when N_Identifier    |
                    N_Expanded_Name =>
                  N := Entity (A);
               when N_Has_Theory |
                    N_Entity     =>
                  N := A;
               when N_Object_Declaration =>
                  N := Defining_Identifier (A);
               when others =>
                  null;
            end case;

            --  We should never depend on discriminants, unless this is the
            --  discriminant of a type declared in a package with external
            --  axioms. In all other cases, we add a reference to the
            --  record instead.

            if Nkind (N) = N_Defining_Identifier
              and then Ekind (N) = E_Discriminant
              and then not SPARK_Util.Is_External_Axioms_Discriminant (N)
            then
               N := Scope (N);
            end if;

            if Present (N) then
               S.Include (N);
            end if;
         end if;
      end Analyze_Ada_Node;

      -----------------
      -- Type_Pre_Op --
      -----------------

      procedure Type_Pre_Op
        (State : in out Search_State;
         Node  : W_Type_Id)
      is
      begin
         if Get_Base_Type (+Node) = EW_Abstract then
            Analyze_Ada_Node (State.S, Get_Ada_Node (+Node));
         end if;
      end Type_Pre_Op;

      -----------------------
      -- Identifier_Pre_Op --
      -----------------------

      procedure Identifier_Pre_Op
        (State : in out Search_State;
         Node  : W_Identifier_Id)
      is
      begin
         Analyze_Ada_Node (State.S, Get_Ada_Node (+Node));
      end Identifier_Pre_Op;

      -----------------------------
      -- Integer_Constant_Pre_Op --
      -----------------------------

      procedure Integer_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Integer_Constant_Id)
      is
         N : constant Node_Id := Get_Ada_Node (+Node);
      begin
         if Present (N)
           and then Nkind (N) in N_Has_Etype
         then
            Analyze_Ada_Node (State.S, Etype (N));
         end if;
      end Integer_Constant_Pre_Op;

      --------------------
      -- Literal_Pre_Op --
      --------------------

      procedure Literal_Pre_Op
        (State : in out Search_State;
         Node  : W_Literal_Id)
      is
      begin
         Analyze_Ada_Node (State.S, Get_Ada_Node (+Node));
      end Literal_Pre_Op;

      --------------------------
      -- Real_Constant_Pre_Op --
      --------------------------

      procedure Real_Constant_Pre_Op
        (State : in out Search_State;
         Node  : W_Real_Constant_Id)
      is
         N : constant Node_Id := Get_Ada_Node (+Node);
      begin
         if Present (N)
           and then Nkind (N) in N_Has_Etype
         then
            Analyze_Ada_Node (State.S, Etype (N));
         end if;
      end Real_Constant_Pre_Op;

      SS : Search_State := (Control => Continue, S => Empty_Set);

   --  Start of Compute_Ada_Nodeset

   begin
      Traverse (SS, +W);
      return SS.S;
   end Compute_Ada_Nodeset;

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

      if With_Completion then
         if Nkind (N) in N_Entity
           and then not Entity_In_External_Axioms (N)
         then
            Add_With_Clause
              (P,
               New_Module
                 (File => No_Name,
                  Name =>
                    NID (Get_Name_String (Get_Name (Module))
                      & Axiom_Theory_Suffix)),
               Use_Kind);
         end if;
      end if;
   end Add_Use_For_Entity;

   ---------------------
   -- Add_With_Clause --
   ---------------------

   procedure Add_With_Clause (T        : W_Theory_Declaration_Id;
                              Module   : W_Module_Id;
                              Use_Kind : EW_Clone_Type;
                              Th_Type  : EW_Theory_Type := EW_Module) is
   begin
      Theory_Declaration_Append_To_Includes
        (T,
         New_Include_Declaration
           (Module   => Module,
            Use_Kind => Use_Kind,
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

            if Has_Record_Type (Typ)
              and then not Entity_In_External_Axioms (Typ)
            then
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
      use Node_Sets;
      S : Set := Compute_Ada_Nodeset (+P.Cur_Theory);

      function Is_Relevant_Node_For_Imports
        (N             : Node_Id;
         Filter_Entity : Node_Id := Empty) return Boolean;
      --  Returns True if N is relevant for theory imports. Filter_Entity is a
      --  node that should not be considered in these imports.

      procedure Add_Definition_Imports (Filter_Entity : Node_Id := Empty);
      --  Adds imports for the definitions of symbols in S

      procedure Add_Axiom_Imports;
      --  Adds imports for the axioms of symbols in S

      procedure Add_Standard_Imports;
      --  Adds imports for the standard Why library

      procedure Record_Dependencies (Defined_Entity : Entity_Id);
      --  Records the dependencies between Defined_Entity and the nodes in S

      -----------------------
      -- Add_Axiom_Imports --
      -----------------------

      procedure Add_Axiom_Imports is
      begin
         for N of S loop
            if Is_Relevant_Node_For_Imports (N) then
               Standard_Imports.Set_SI (N);
               Add_Use_For_Entity (P, N, With_Completion => True);
            end if;
         end loop;
      end Add_Axiom_Imports;

      ----------------------------
      -- Add_Definition_Imports --
      ----------------------------

      procedure Add_Definition_Imports (Filter_Entity : Node_Id := Empty) is
      begin
         for N of S loop
            if Is_Relevant_Node_For_Imports (N, Filter_Entity) then
               Standard_Imports.Set_SI (N);
               Add_Use_For_Entity (P, N, With_Completion => False);
            end if;
         end loop;
      end Add_Definition_Imports;

      --------------------------
      -- Add_Standard_Imports --
      --------------------------

      procedure Add_Standard_Imports is
         --  We add the dependencies to Gnatprove_Standard theories that may
         --  have been triggered
         use Standard_Imports;
      begin
         for Index in Imports'Range loop
            if Imports (Index) then
               Add_With_Clause
                 (P,
                  To_Module (Index),
                  EW_Clone_Default);

               --  Two special cases for infix symbols; these are the only
               --  theories (as opposed to modules) that are used, and the
               --  only ones to be "use import"ed

               if Index = SI_Integer then
                  Add_With_Clause (P.Cur_Theory,
                                   Int_Module,
                                   EW_Import,
                                   EW_Theory);
               elsif Index = SI_Float then
                  Add_With_Clause (P.Cur_Theory,
                                   RealInfix,
                                   EW_Import,
                                   EW_Theory);
               end if;
            end if;
         end loop;
      end Add_Standard_Imports;

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
         for N of S loop
            if Is_Relevant_Node_For_Imports (N) then
               Add_To_Graph (Entity_Dependencies, Defined_Entity, N);
            end if;
         end loop;
      end Record_Dependencies;

   --  Start of Close_Theory

   begin
      Standard_Imports.Clear;
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
               Standard_Imports.Set_SI (Defined_Entity);
               Record_Dependencies (Defined_Entity);
            end if;
            Add_Definition_Imports (Filter_Entity => Defined_Entity);
            Add_Standard_Imports;

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
            Add_Standard_Imports;

         --  case 4: a theory for generating VCs

         --  Add to S the set of all axioms used transitively to define symbols
         --  in the current theory. Add imports for all symbols used and their
         --  axioms. Add standard imports.

         when VC_Generation_Theory =>
            S.Union (Get_Graph_Closure (Entity_Dependencies, S));
            Add_Axiom_Imports;
            Add_Standard_Imports;
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
      --  Theories for nodes that are not entities should never depend on
      --  variables.

      if Nkind (E) in N_Has_Theory then
         return WF_Pure;
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
                 and then not Flow.Utility.Has_Proof_Global_Reads (Decl_E)
                 and then not Flow.Utility.Has_Proof_Global_Writes (Decl_E)
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
   begin
      case Ekind (E) is
         when Object_Kind =>
            if not Is_Mutable_In_Why (E) then

               --  Theories which depend on variables are defined in context
               --  files.

               if Expression_Depends_On_Variables
                 (Expression (Parent (Unique_Entity (E))))
               then
                  return WF_Context;

               --  Theories which do not depend on variables are defined in
               --  type files.

               else
                  return WF_Pure;
               end if;

            else
               return Dispatch_Entity (E);
            end if;

         when others =>
            return Dispatch_Entity (E);
      end case;
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
         N1 : constant W_Identifier_Id := Get_Name (+Left);
         N2 : constant W_Identifier_Id := Get_Name (+Right);
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
      elsif Ekind (N) in Private_Kind
        or else Has_Private_Declaration (N)
      then
         if Entity_In_External_Axioms (N) then
            return New_Kind_Base_Type (N, Kind);
         elsif Entity_In_SPARK (MUT (N)) then
            if MUT (N) = N then
               return New_Kind_Base_Type (N, Kind);
            else
               return EW_Abstract (MUT (N));
            end if;
         else
            return EW_Private_Type;
         end if;
      elsif not Entity_In_SPARK (N) then
         return EW_Private_Type;
      else
         return New_Kind_Base_Type (N, Kind);
      end if;
   end EW_Abstract_Shared;

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

   -----------------
   -- Get_EW_Type --
   -----------------

   function Get_EW_Type (T : W_Type_Id) return EW_Type is
   begin
      if Get_Kind (+T) = W_Type then
         return Get_Base_Type (+T);
      else
         return EW_Abstract;
      end if;
   end Get_EW_Type;

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
         when Real_Kind =>
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
            if Entity_In_External_Axioms (Ty) then
               return EW_Abstract;
            elsif Entity_In_SPARK (MUT (Ty)) then
               return Get_EW_Term_Type (MUT (Ty));
            else
               return EW_Private;
            end if;

         when others =>
            return EW_Abstract;
      end case;
   end Get_EW_Term_Type;

   --------------------------
   -- Is_Record_Conversion --
   --------------------------

   function Is_Record_Conversion (Left, Right : W_Type_Id) return Boolean
   is (Get_Base_Type (Base_Why_Type (Left)) in EW_Abstract | EW_Split and then
       Get_Base_Type (Base_Why_Type (Right)) in EW_Abstract | EW_Split and then
       Has_Record_Type (Get_Ada_Node (+Left)) and then
       Has_Record_Type (Get_Ada_Node (+Right)));

   -------------------------
   -- Is_Array_Conversion --
   -------------------------

   function Is_Array_Conversion (Left, Right : W_Type_Id) return Boolean
   is (Get_Base_Type (Base_Why_Type (Left)) in EW_Abstract | EW_Split and then
       Get_Base_Type (Base_Why_Type (Right)) in EW_Abstract | EW_Split and then
       Has_Array_Type (Get_Ada_Node (+Left)) and then
       Has_Array_Type (Get_Ada_Node (+Right)));

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
                          Name       => To_Why_Id (E));
      else
         return New_Type (Ada_Node   => E,
                          Is_Mutable => False,
                          Base_Type  => EW_Split,
                          Name       =>
                            New_Identifier
                              (Ada_Node => E,
                               Name     => "__split",
                               Module   => E_Module (E)));
      end if;
   end New_Kind_Base_Type;

   --------------------
   -- New_Named_Type --
   --------------------

   function New_Named_Type (Name : W_Identifier_Id) return W_Type_Id is
   begin
      return New_Type (Ada_Node   => Empty,
                       Is_Mutable => False,
                       Base_Type  => EW_Abstract,
                       Name       => Name);
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
                          Name    : String;
                          Comment : String;
                          Kind    : EW_Theory_Type := EW_Module)
   is
      S : constant String := Capitalize_First (Name);
   begin
      P.Cur_Theory :=
        New_Theory_Declaration (Name    => NID (S),
                                Kind    => Kind,
                                Comment => NID (Comment));
   end Open_Theory;

   ---------------
   -- To_Why_Id --
   ---------------

   function To_Why_Id (E      : Entity_Id;
                       Domain : EW_Domain := EW_Prog;
                       Local  : Boolean := False;
                       Rec    : Entity_Id := Empty;
                       Typ    : W_Type_Id := Why_Empty) return W_Identifier_Id
   is
      Suffix : constant String :=
        (if Ekind (E) in Subprogram_Kind | E_Subprogram_Body
              and then Domain = EW_Prog
         then
            Short_Name (E)
         elsif Ekind (E) in Subprogram_Kind
                          | E_Subprogram_Body
                          | Named_Kind
                          | Type_Kind
                          | Object_Kind
                          | E_Abstract_State
         then
            Short_Name (E)
         elsif Ekind (E) = E_Loop then
            Capitalize_First (Short_Name (E))
         else "");
   begin

      --  The component case is sufficiently different to treat it
      --  independently

      if Ekind (E) in E_Component | E_Discriminant then
         declare
            Field : constant String :=
              "rec__" & Get_Name_String (Chars (E));
            Ada_N : constant Node_Id :=
              (if Rec = Empty then Unique_Entity (Scope (E)) else Rec);
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
                    Module  => E_Module (Ada_N),
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
         return
           New_Identifier
             (Ada_Node => E,
              Name     => Suffix,
              Module   => E_Module (E),
              Typ      => Typ);
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

   function To_Why_Type (T : String) return W_Identifier_Id
   is
   begin
      if T = SPARK_Xrefs.Name_Of_Heap_Variable then
         return New_Identifier (Name => "__type_of_heap");
      else
         return
           Prefix (New_Module (File => No_Name, Name => NID (T)),
                   WNE_Type);
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

   ---------------
   -- Why_Types --
   ---------------

   function Why_Types (E : EW_Basic_Type) return W_Type_Id is
   begin
      if Why_Types_Array (E) /= Why_Empty then
         return Why_Types_Array (E);
      end if;
      Why_Types_Array (E) :=
        New_Type (Ada_Node   => Empty,
                       Base_Type  => E,
                       Is_Mutable => False,
                       Name       => New_Identifier (Name => Img (E)));
      return Why_Types_Array (E);
   end Why_Types;

begin
   Type_Hierarchy.Move_Child (EW_Unit, EW_Real);
   Type_Hierarchy.Move_Child (EW_Int, EW_Bool);
   Type_Hierarchy.Move_Child (EW_Real, EW_Int);
   Type_Hierarchy.Freeze;
end Why.Inter;
