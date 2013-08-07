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

with AA_Util;             use AA_Util;
with Einfo;               use Einfo;
with Namet;               use Namet;
with Sem_Util;            use Sem_Util;
with SPARK_Xrefs;         use SPARK_Xrefs;
with Stand;               use Stand;
with String_Utils;        use String_Utils;
with Constant_Tree;

with SPARK_Definition;    use SPARK_Definition;
with SPARK_Util;          use SPARK_Util;

with Why.Conversions;     use Why.Conversions;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Atree.Tables;    use Why.Atree.Tables;
with Why.Atree.Traversal; use Why.Atree.Traversal;
with Why.Gen.Names;       use Why.Gen.Names;

with Gnat2Why.Util;       use Gnat2Why.Util;

---------------
-- Why.Inter --
---------------

package body Why.Inter is

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Compute_Ada_Nodeset (W : Why_Node_Id) return
     Node_Sets.Set;
   --  For a given Why node, compute the required Ada nodes, from which we can
   --  compute the necessary inclusions on the Why side

   subtype N_Has_Theory is Node_Kind with
     Static_Predicate => N_Has_Theory in N_String_Literal |
                                         N_Aggregate      |
                                         N_Slice;
   --  Subtype of nodes (instead of entities) which have an associated theory,
   --  and should be treated specially.

   package Type_Hierarchy is
     new Constant_Tree (EW_Base_Type, EW_Unit);

   function Extract_Object_Name (Obj : String) return String;
   --  Extract the name after the last "__"; return Obj when the string does
   --  not contain "__". This is useful to determine the user name of an Ada
   --  entity when all we have is its fully scoped name (for hidden effects of
   --  other units).

   function Get_EW_Term_Type (N : Node_Id) return EW_Type;

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

      function To_String (E : Standard_Imports_Enum) return String;

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
              not Entity_In_SPARK (UE) then
               return;
            end if;
            if Ekind (UE) in Type_Kind and then not Entity_In_SPARK (UE) then
               return;
            end if;

            --  Only Standard.Boolean is modeled as bool; any other boolean
            --  subtype is modeled as an abstract type to have range checks.

            if UE = Standard_Boolean then
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
                  if Entity_In_SPARK (Most_Underlying_Type (UE)) then
                     Set_SI_Internal (Most_Underlying_Type (UE));
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

      function To_String (E : Standard_Imports_Enum) return String is
      begin
         case E is
            when SI_Integer => return "Integer";
            when SI_Float   => return "Floating";
            when SI_Boolean => return "Boolean";
            when SI_Array1  => return "Array__1";
            when SI_Array2  => return "Array__2";
            when SI_Array3  => return "Array__3";
            when SI_Array4  => return "Array__4";
         end case;
      end To_String;

   end Standard_Imports;

   --------------------
   -- Add_Completion --
   --------------------

   procedure Add_Completion
     (Name            : String;
      Completion_Name : String;
      Kind            : Why_Context_File_Enum)
   is
      Unb_Name : constant Unbounded_String := To_Unbounded_String (Name);
      Unb_Comp : constant Unbounded_String :=
        To_Unbounded_String (Completion_Name);
      Completions  : Why_File_Completion_Lists.List;
   begin
      pragma Assert (Unb_Name /= Unb_Comp);

      if not Why_File_Completion.Contains (Unb_Name) then
         Completions := Why_File_Completion_Lists.Empty_List;
      else
         Completions := Why_File_Completion.Element (Unb_Name);
      end if;

      Completions.Append (Why_File_Completion_Item'(Name => Unb_Comp,
                                                    Kind => Kind));

      Why_File_Completion.Include (Key      => Unb_Name,
                                   New_Item => Completions);
   end Add_Completion;

   -------------------------
   -- Compute_Ada_Nodeset --
   -------------------------

   function Compute_Ada_Nodeset (W : Why_Node_Id) return Node_Sets.Set is
      use Node_Sets;

      type Search_State is new Traversal_State with record
         S : Set;
      end record;

      procedure Base_Type_Pre_Op
        (State : in out Search_State;
         Node  : W_Base_Type_Id);

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

      ----------------------
      -- Base_Type_Pre_Op --
      ----------------------

      procedure Base_Type_Pre_Op
        (State : in out Search_State;
         Node  : W_Base_Type_Id)
      is
      begin
         if Get_Base_Type (+Node) = EW_Abstract then
            Analyze_Ada_Node (State.S, Get_Ada_Node (+Node));
         end if;
      end Base_Type_Pre_Op;

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

   ---------------------
   -- Get_Completions --
   ---------------------

   function Get_Completions
     (Name       : String;
      Up_To_Kind : Why_File_Enum) return Why_Completions
   is
      function Num_Compl (L : Why_File_Completion_Lists.List) return Natural;
      --  Find the number of completions from L

      procedure Get_Compl
        (L           :        Why_File_Completion_Lists.List;
         Position    : in out Natural;
         Completions : in out Why_Completions);
      --  Find all the completions from L

      ---------------
      -- Num_Compl --
      ---------------

      function Num_Compl (L : Why_File_Completion_Lists.List) return Natural is
         Count : Natural := 0;
      begin
         for Compl of L loop
            if Compl.Kind <= Up_To_Kind then
               Count := Count + 1;

               if Why_File_Completion.Contains (Compl.Name) then
                  Count := Count +
                    Num_Compl (Why_File_Completion.Element (Compl.Name));
               end if;
            end if;
         end loop;

         return Count;
      end Num_Compl;

      ---------------
      -- Get_Compl --
      ---------------

      procedure Get_Compl
        (L           :        Why_File_Completion_Lists.List;
         Position    : in out Natural;
         Completions : in out Why_Completions) is
      begin
         for Compl of L loop
            if Compl.Kind <= Up_To_Kind then
               Completions (Position) := Compl;
               Position := Position + 1;
               if Why_File_Completion.Contains (Compl.Name) then
                  Get_Compl (Why_File_Completion.Element (Compl.Name),
                             Position, Completions);
               end if;
            end if;
         end loop;
      end Get_Compl;

      Unb_Name : constant Unbounded_String := To_Unbounded_String (Name);
      Count : Natural;
      Direct_Completions : Why_File_Completion_Lists.List;

   --  Start of Get_Completions

   begin
      if Why_File_Completion.Contains (Unb_Name) then
         Direct_Completions := Why_File_Completion.Element (Unb_Name);

         --  Find the number of completions for Name

         Count := Num_Compl (Direct_Completions);

         --  Return all completions

         declare
            Completions : Why_Completions (1 .. Count);
            Position    : Positive := 1;
         begin
            Get_Compl (Direct_Completions, Position, Completions);
            return Completions;
         end;

      else
         declare
            Completions : Why_Completions (1 .. 0);
         begin
            return Completions;
         end;
      end if;
   end Get_Completions;

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
               F : constant Entity_Name := File_Of_Entity (Var);
               S : constant String := Capitalize_First (Var.all);
            begin
               Add_With_Clause (T,
                                File_Name_Without_Suffix (F.all) &
                                  Why_File_Suffix (WF_Variables),
                                S,
                                EW_Clone_Default);
            end;
         end if;
      end loop;
   end Add_Effect_Imports;

   ------------------------
   -- Add_Effect_Imports --
   ------------------------

   procedure Add_Effect_Imports (P : in out Why_File;
                                 S : Name_Set.Set)
   is
   begin
      Add_Effect_Imports (P.Cur_Theory, S);
   end Add_Effect_Imports;

   ------------------------
   -- Add_Use_For_Entity --
   ------------------------

   procedure Add_Use_For_Entity
     (P               : in out Why_File;
      N               : Entity_Id;
      Use_Kind        : EW_Clone_Type := EW_Clone_Default;
      With_Completion : Boolean := True)
   is
      function Import_Type_Of_Entity (E : Entity_Id) return EW_Clone_Type;
      --  return the import type that is used for such an entity

      ---------------------------
      -- Import_Type_Of_Entity --
      ---------------------------

      function Import_Type_Of_Entity (E : Entity_Id) return EW_Clone_Type is
      begin
         if Nkind (E) in N_Has_Etype then
            return EW_Import;
         end if;
         return EW_Clone_Default;
      end Import_Type_Of_Entity;

      File_Name   : constant String :=
        File_Base_Name_Of_Entity (N)
        & Why_File_Suffix (Dispatch_Entity (N));
      Raw_Name    : constant String := Name_Of_Node (N);
      Theory_Name : constant String := Capitalize_First (Raw_Name);
      Import      : constant EW_Clone_Type :=
        (if Use_Kind = EW_Clone_Default then Import_Type_Of_Entity (N)
         else Use_Kind);

   --  Start of Add_Use_For_Entity

   begin
      --  In the few special cases for which the Full_Name of N is not based on
      --  its Unique_Name, the corresponding theories are standard ones (dealt
      --  with separately). Return in that case, to avoid generating wrong
      --  includes based on a non-unique Full_Name.

      if Full_Name_Is_Not_Unique_Name (N) then
         return;
      end if;

      if File_Name /= P.Name.all then
         Add_With_Clause (P, File_Name, Theory_Name, Import);
      else
         Add_With_Clause (P, "", Theory_Name, Import);
      end if;

      if With_Completion then
         declare
            Completions  : constant Why_Completions :=
              Get_Completions (Raw_Name, Up_To_Kind => P.Kind);
         begin
            for J in Completions'Range loop
               declare
                  Compl_Fname  : constant String :=
                    File_Base_Name_Of_Entity (N)
                    & Why_File_Suffix (Completions (J).Kind);
                  Compl_Name : constant String :=
                    Capitalize_First (To_String (Completions (J).Name));
               begin
                  if Compl_Fname /= P.Name.all then
                     Add_With_Clause
                       (P, Compl_Fname, Compl_Name, Import);
                  else
                     Add_With_Clause (P, "", Compl_Name, Import);
                  end if;
               end;
            end loop;
         end;
      end if;
   end Add_Use_For_Entity;

   ---------------------
   -- Add_With_Clause --
   ---------------------

   procedure Add_With_Clause (T        : W_Theory_Declaration_Id;
                              File     : String;
                              T_Name   : String;
                              Use_Kind : EW_Clone_Type;
                              Th_Type  : EW_Theory_Type := EW_Module) is
      File_Ident : constant W_Identifier_Id :=
        (if File = "" then Why_Empty else New_Identifier (Name => File));
   begin
      Theory_Declaration_Append_To_Includes
        (T,
         New_Include_Declaration (File     => File_Ident,
                                  T_Name   => New_Identifier (Name => T_Name),
                                  Use_Kind => Use_Kind,
                                  Kind     => Th_Type));
   end Add_With_Clause;

   procedure Add_With_Clause (P        : in out Why_File;
                              File     : String;
                              T_Name   : String;
                              Use_Kind : EW_Clone_Type;
                              Th_Type  : EW_Theory_Type := EW_Module) is
   begin
      Add_With_Clause (P.Cur_Theory, File, T_Name, Use_Kind, Th_Type);
   end Add_With_Clause;

   procedure Add_With_Clause (P        : in out Why_File;
                              Other    : Why_File;
                              Use_Kind : EW_Clone_Type) is
   begin
      Add_With_Clause (P, Other.Name.all, "Main", Use_Kind);
   end Add_With_Clause;

   -------------------
   -- Base_Why_Type --
   -------------------

   function Base_Why_Type (W : W_Base_Type_Id) return W_Base_Type_Id is
      Kind : constant EW_Type := Get_Base_Type (W);
   begin
      case Kind is
         when EW_Abstract =>
            return Base_Why_Type (Get_Ada_Node (+W));
         when others =>
            return W;
      end case;
   end Base_Why_Type;

   function Base_Why_Type (N : Node_Id) return W_Base_Type_Id is

      E   : constant EW_Type := Get_EW_Term_Type (N);
      Typ : constant Entity_Id := Etype (N);
   begin
      case E is
         when EW_Abstract =>
            if Is_Record_Type (Typ) then
               return EW_Abstract (Root_Record_Type (Typ));
            else
               return EW_Abstract (Typ);
            end if;
         when others =>
            return Why_Types (E);
      end case;
   end Base_Why_Type;

   function Base_Why_Type (Left, Right : W_Base_Type_Id) return W_Base_Type_Id
   is
   begin
      return LCA (Base_Why_Type (Left), Base_Why_Type (Right));
   end Base_Why_Type;

   function Base_Why_Type (Left, Right : Node_Id) return W_Base_Type_Id is
   begin
      return Base_Why_Type (Base_Why_Type (Left), Base_Why_Type (Right));
   end Base_Why_Type;

   ------------------
   -- Close_Theory --
   ------------------

   procedure Close_Theory
     (P               : in out Why_File;
      Filter_Entity   : Entity_Id;
      Defined_Entity  : Entity_Id := Empty;
      Do_Closure      : Boolean := False;
      No_Import       : Boolean := False;
      With_Completion : Boolean := True)
   is
      use Node_Sets;
      S : Set := Compute_Ada_Nodeset (+P.Cur_Theory);

      Gnatprove_Standard : constant String := "_gnatprove_standard";

   begin
      --  If required, compute the closure of entities on which Defined_Entity
      --  depends, and add those in the set of nodes S used for computing
      --  includes.

      if Do_Closure then
         S.Union (Get_Graph_Closure (Entity_Dependencies, Defined_Entity));
      end if;

      Standard_Imports.Clear;
      Add_With_Clause (P, Gnatprove_Standard, "Main", EW_Import);

      if not (No_Import) then

         if Present (Filter_Entity) then
            Standard_Imports.Set_SI (Filter_Entity);
         end if;

         --  S contains all mentioned Ada entities; for each, we get the
         --  unit where it was defined and add it to the unit set

         for N of S loop
            --  Here we need to consider entities and some non-entities
            --  such as string literals. We do *not* consider the
            --  Filter_Entity, nor its Full_View. Loop parameters are a
            --  bit special, we want to deal with them only if they are
            --  from loop, but not from a quantifier.

            if N /= Filter_Entity
              and then
                (if Nkind (N) in N_Entity and then Is_Full_View (N) then
                 Partial_View (N) /= Filter_Entity)
              and then
                (if Nkind (N) in N_Entity and then
                 Ekind (N) = E_Loop_Parameter
                 then not Is_Quantified_Loop_Param (N))
            then
               Standard_Imports.Set_SI (N);
               Add_Use_For_Entity (P, N, With_Completion => With_Completion);

               --  When Defined_Entity is present, add the entities on which it
               --  depends in the graph of dependencies.

               if Present (Defined_Entity) then
                  Add_To_Graph (Entity_Dependencies, Defined_Entity, N);
               end if;
            end if;
         end loop;

         --  We add the dependencies to Gnatprove_Standard theories that may
         --  have been triggered

         declare
            use Standard_Imports;
         begin
            for Index in Imports'Range loop
               if Imports (Index) then
                  Add_With_Clause (P,
                                   Gnatprove_Standard,
                                   To_String (Index),
                                   EW_Clone_Default);

                  --  Two special cases for infix symbols; these are the only
                  --  theories (as opposed to modules) that are used, and the
                  --  only ones to be "use import"ed

                  if Index = SI_Integer then
                     Add_With_Clause (P,
                                      "int",
                                      "Int",
                                      EW_Import,
                                      EW_Theory);
                  elsif Index = SI_Float then
                     Add_With_Clause (P,
                                      "real",
                                      "RealInfix",
                                      EW_Import,
                                      EW_Theory);
                  end if;
               end if;
            end loop;
         end;
      end if;

      File_Append_To_Theories (P.File, +P.Cur_Theory);
      P.Cur_Theory := Why_Empty;
   end Close_Theory;

   --------------------
   -- Discard_Theory --
   --------------------

   procedure Discard_Theory (P : in out Why_File) is
   begin
      P.Cur_Theory := Why_Empty;
   end Discard_Theory;

   ---------------------
   -- Dispatch_Entity --
   ---------------------

   function Dispatch_Entity (E : Entity_Id) return Why_File_Enum is
   begin
      if Nkind (E) in N_Has_Theory then

         --  Theories which depend on variables are defined in context files

         if Expression_Depends_On_Variables (E) then
            if In_Main_Unit_Spec (E) then
               return WF_Context_In_Spec;
            else
               pragma Assert (In_Main_Unit_Body (E));
               return WF_Context_In_Body;
            end if;

         --  Theories which do not depend on variables are defined in type
         --  files.

         else
            if In_Main_Unit_Spec (E) then
               return WF_Types_In_Spec;
            else
               pragma Assert (In_Main_Unit_Body (E));
               return WF_Types_In_Body;
            end if;
         end if;
      end if;

      case Ekind (E) is
         when Named_Kind  =>
            if In_Some_Unit_Body (Parent (E)) then
               return WF_Context_In_Body;
            else
               return WF_Context_In_Spec;
            end if;

         when Subprogram_Kind | E_Subprogram_Body =>
            declare
               Decl_E : constant Entity_Id := Unique_Entity (E);

               --  If the subprogram reads or writes a variables in an outter
               --  scope, it cannot be declared in the "type" Why file, as it
               --  needs visibility over the "variable" Why file.

               Has_Effects : constant Boolean :=
                 Has_Global_Reads (Decl_E)
                   or else Has_Global_Writes (Decl_E);
            begin
               --  Subprograms without read/write global effects are declared
               --  in the "type" Why files instead of the "context" Why files,
               --  so that they can be used as parameters of generics whose
               --  axiomatization in Why is written manually (example: formal
               --  containers).

               if In_Some_Unit_Body (Parent (E)) then
                  if Has_Effects then
                     return WF_Context_In_Body;
                  else
                     return WF_Types_In_Body;
                  end if;
               else
                  if Has_Effects then
                     return WF_Context_In_Spec;
                  else
                     return WF_Types_In_Spec;
                  end if;
               end if;
            end;

         when Object_Kind =>

            --  Constants are defined in type files. Their defining axiom, if
            --  any, is defined as a completion in the type or context file.

            if not Is_Mutable_In_Why (E) then
               if In_Main_Unit_Body (E) then
                  return WF_Types_In_Body;
               else
                  return WF_Types_In_Spec;
               end if;

            elsif Ekind (E) = E_Discriminant
              and then Is_External_Axioms_Discriminant (E)
            then
               if In_Main_Unit_Body (E) then
                  return WF_Context_In_Body;
               else
                  return WF_Context_In_Spec;
               end if;

            else
               return WF_Variables;
            end if;

         when Type_Kind =>
            declare
               Real_Node : constant Node_Id :=
                (if Is_Itype (E) then Associated_Node_For_Itype (E) else E);
            begin
               if In_Main_Unit_Body (Real_Node) then
                  return WF_Types_In_Body;
               else
                  return WF_Types_In_Spec;
               end if;
            end;

         when E_Package =>
            if In_Some_Unit_Body (Parent (E)) then
               return WF_Types_In_Body;
            else
               return WF_Types_In_Spec;
            end if;

         when E_Loop =>
            return WF_Context_In_Body;

         when others =>
            raise Program_Error;
      end case;
   end Dispatch_Entity;

   --------------------------------
   -- Dispatch_Entity_Completion --
   --------------------------------

   function Dispatch_Entity_Completion (E : Entity_Id) return Why_File_Enum is
   begin
      case Ekind (E) is
         when Object_Kind =>
            if not Is_Mutable_In_Why (E) then

               --  Theories which depend on variables are defined in context
               --  files.

               if Expression_Depends_On_Variables
                 (Expression (Parent (Unique_Entity (E))))
               then
                  if In_Main_Unit_Body (E) then
                     return WF_Context_In_Body;
                  else
                     return WF_Context_In_Spec;
                  end if;

               --  Theories which do not depend on variables are defined in
               --  type files.

               else
                  if In_Main_Unit_Body (E) then
                     return WF_Types_In_Body;
                  else
                     return WF_Types_In_Spec;
                  end if;
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

   function Eq (Left, Right : W_Base_Type_Id) return Boolean is
      Left_Kind  : constant EW_Type := Get_Base_Type (Left);
      Right_Kind : constant EW_Type := Get_Base_Type (Right);
   begin
      if Left_Kind /= Right_Kind then
         return False;
      end if;

      return Left_Kind /= EW_Abstract
        or else Eq (Get_Ada_Node (+Left), Get_Ada_Node (+Right));
   end Eq;

   ------------------
   -- Eq_Base_Type --
   ------------------

   function Eq_Base_Type (Left, Right : W_Primitive_Type_Id) return Boolean is
   begin
      return Get_Kind (+Left) = W_Base_Type
        and then Get_Kind (+Right) = W_Base_Type
        and then Eq (+Left, +Right);
   end Eq_Base_Type;

   -----------------
   -- EW_Abstract --
   -----------------

   function EW_Abstract (N : Node_Id) return W_Base_Type_Id is
   begin
      if N = Standard_Boolean then
         return EW_Bool_Type;
      elsif N = Universal_Fixed then
         return EW_Real_Type;

      --  Private types that are not in SPARK should be translated at the
      --  special __private abstract type. Other private types should be
      --  translated into the most underlying type.

      elsif Ekind (N) in Private_Kind
        or else Has_Private_Declaration (N)
      then
         if Entity_In_External_Axioms (N) then
            return New_Base_Type (Base_Type => EW_Abstract, Ada_Node => N);
         else
            declare
               Under_Typ : constant Entity_Id := Most_Underlying_Type (N);
            begin
               if Entity_In_SPARK (Under_Typ) then

                  --  Avoid infinite recursion if the private type is its own
                  --  most underlying type. Return the expected abstract type
                  --  directly.

                  if Under_Typ = N then
                     return New_Base_Type (Base_Type => EW_Abstract,
                                           Ada_Node  => N);

                  --  Recurse with the most underlying type

                  else
                     return EW_Abstract (Under_Typ);
                  end if;

               --  The underlying type is not in SPARK, return the special
               --  __private abstract type.

               else
                  return New_Base_Type (Base_Type => EW_Private);
               end if;
            end;
         end if;

      --  Normal case: the type is translated into its own abstract type

      else
         return New_Base_Type (Base_Type => EW_Abstract, Ada_Node => N);
      end if;
   end EW_Abstract;

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

   ------------------------------
   -- File_Base_Name_Of_Entity --
   ------------------------------

   function File_Base_Name_Of_Entity (E : Entity_Id) return String is
      U : Node_Id;
   begin
      if Is_In_Standard_Package (E) then
         return Standard_Why_Package_Name;
      end if;
      U := Enclosing_Comp_Unit_Node (E);

      --  Itypes are not attached to the tree, so we go through the
      --  associated node

      if not Present (U) and then Is_Itype (E) then
         U := Enclosing_Comp_Unit_Node (Associated_Node_For_Itype (E));
      end if;

      --  Special handling for entities of subunits, we extract the library
      --  unit

      while Nkind (Unit (U)) = N_Subunit loop
         U := Library_Unit (U);
      end loop;
      return Spec_File_Name_Without_Suffix (U);
   end File_Base_Name_Of_Entity;

   ---------------
   -- Full_Name --
   ---------------

   function Full_Name (N : Entity_Id) return String is
   begin
      --  In special cases, return a fixed name. These cases should match those
      --  for which Full_Name_Is_Not_Unique_Name returns True.

      if Full_Name_Is_Not_Unique_Name (N) then
         if N = Standard_Boolean then
            return "bool";
         elsif N = Universal_Fixed then
            return "real";
         else
            raise Program_Error;
         end if;

      --  In the general case, return a name based on the Unique_Name

      else
         declare
            S : String := Unique_Name (N);
         begin

            --  In Why3, enumeration literals need to be upper case. Why2
            --  doesn't care, so we enforce upper case here

            if Ekind (N) = E_Enumeration_Literal then
               Capitalize_First (S);
            end if;
            return S;
         end;
      end if;
   end Full_Name;

   ----------------------------------
   -- Full_Name_Is_Not_Unique_Name --
   ----------------------------------

   function Full_Name_Is_Not_Unique_Name (N : Entity_Id) return Boolean is
   begin
      return N = Standard_Boolean or else N = Universal_Fixed;
   end Full_Name_Is_Not_Unique_Name;

   -----------------
   -- Get_EW_Type --
   -----------------

   function Get_EW_Type (T : W_Primitive_Type_Id) return EW_Type is
   begin
      if Get_Kind (+T) = W_Base_Type then
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
        or else not (Ekind (N) in Type_Kind) then
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

            if Ty = Standard_Boolean then
               return EW_Bool;
            elsif Ty = Universal_Fixed then
               return EW_Real;
            else
               return EW_Int;
            end if;

         when Private_Kind =>
            if Entity_In_External_Axioms (Ty) then
               return EW_Abstract;
            elsif Entity_In_SPARK (Most_Underlying_Type (Ty)) then
               return Get_EW_Term_Type (Most_Underlying_Type (Ty));
            else
               return EW_Private;
            end if;

         when others =>
            return EW_Abstract;
      end case;
   end Get_EW_Term_Type;

   --------------------
   -- Init_Why_Files --
   --------------------

   procedure Init_Why_Files (Unit : Node_Id) is
      Spec_Prefix : constant String := Spec_File_Name_Without_Suffix (Unit);
      Body_Prefix : constant String := Body_File_Name_Without_Suffix (Unit);
   begin

      --  We cannot assume that spec and body use the same file basename. So we
      --  force to use the spec filename everywhere. The "main" Why3 file is
      --  special: the builder expects it to have the basename of the body.
      --  That's not a problem, we can use the body name because this file will
      --  never be referenced by other Why3 files.

      for Kind in WF_Types_In_Spec .. WF_Context_In_Body loop
         Why_Files (Kind) :=
           Make_Empty_Why_File (Name => Spec_Prefix & Why_File_Suffix (Kind),
                                Kind => Kind);
      end loop;
      Why_Files (WF_Main) :=
        Make_Empty_Why_File (Name => Body_Prefix & Why_File_Suffix (WF_Main),
                             Kind => WF_Main);
   end Init_Why_Files;

   procedure Init_Why_Files (Prefix : String) is
   begin
      for Kind in Why_File_Enum loop
         Why_Files (Kind) :=
           Make_Empty_Why_File (Name => Prefix & Why_File_Suffix (Kind),
                                Kind => Kind);
      end loop;
   end Init_Why_Files;

   --------------------------
   -- Is_Record_Conversion --
   --------------------------

   function Is_Record_Conversion (Left, Right : W_Base_Type_Id) return Boolean
   is (Get_Base_Type (Base_Why_Type (Left)) = EW_Abstract and then
       Get_Base_Type (Base_Why_Type (Right)) = EW_Abstract and then
       Is_Record_Type (Get_Ada_Node (+Left)) and then
       Is_Record_Type (Get_Ada_Node (+Right)));

   -------------------------
   -- Is_Array_Conversion --
   -------------------------

   function Is_Array_Conversion (Left, Right : W_Base_Type_Id) return Boolean
   is (Get_Base_Type (Base_Why_Type (Left)) = EW_Abstract and then
       Get_Base_Type (Base_Why_Type (Right)) = EW_Abstract and then
       Is_Array_Type (Get_Ada_Node (+Left)) and then
       Is_Array_Type (Get_Ada_Node (+Right)));

   ---------
   -- LCA --
   ---------

   function LCA
     (Left  : W_Base_Type_Id;
      Right : W_Base_Type_Id;
      Force : Boolean := False) return W_Base_Type_Id
   is
      Left_Base, Right_Base : EW_Type;

   begin
      if not Force and then Eq (Left, Right) then
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
   -- Make_Empty_Why_File --
   -------------------------

   function Make_Empty_Why_File
     (Name : String;
      Kind : Why_File_Enum) return Why_File is
   begin
      return Why_File'(Name       => new String'(Name),
                       File       => New_File,
                       Kind       => Kind,
                       Cur_Theory => Why_Empty);
   end Make_Empty_Why_File;

   ------------------
   -- Name_Of_Node --
   ------------------

   function Name_Of_Node (N : Node_Id) return String is
   begin
      if Nkind (N) in N_Has_Theory then
         return New_Sloc_Ident (N);
      end if;
      return Full_Name (N);
   end Name_Of_Node;

   -----------------
   -- Open_Theory --
   -----------------

   procedure Open_Theory (P       : in out Why_File;
                          Name    : String;
                          Comment : String;
                          Kind    : EW_Theory_Type := EW_Module)
   is
      S : constant String := Capitalize_First (Name);
   begin
      P.Cur_Theory :=
        New_Theory_Declaration (Name    => New_Identifier (Name => S),
                                Kind    => Kind,
                                Comment => New_Identifier (Name => Comment));
   end Open_Theory;

   ---------------
   -- To_Why_Id --
   ---------------

   function To_Why_Id (E      : Entity_Id;
                       Domain : EW_Domain := EW_Prog;
                       Local  : Boolean := False;
                       Rec    : Entity_Id := Empty) return W_Identifier_Id
   is
      Suffix : constant String :=
        (if Ekind (E) in Subprogram_Kind | E_Subprogram_Body and then
         Domain = EW_Prog then Short_Name (E)
         elsif Ekind (E) in Subprogram_Kind | E_Subprogram_Body |
         Named_Kind | Type_Kind | Object_Kind then
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
                                      Name     => Field);
            else
               return New_Identifier (Ada_Node => Ada_N,
                                      Name     => Field,
                                      Context  => Full_Name (Ada_N));
            end if;
         end;
      elsif Local then
         return New_Identifier (Ada_Node => E, Name => Suffix);
      elsif Suffix = "" then
         return New_Identifier (Ada_Node => E,
                                Name     => Full_Name (E));
      else
         return
           New_Identifier (Ada_Node => E,
                           Name     => Suffix,
                           Context => Full_Name (E));
      end if;
   end To_Why_Id;

   function To_Why_Id (Obj : String) return W_Identifier_Id
   is
   begin
      if Obj = SPARK_Xrefs.Name_Of_Heap_Variable then
         return New_Identifier (Name => SPARK_Xrefs.Name_Of_Heap_Variable);
      else
         return Prefix (Obj, Avoid_Why3_Keyword (Extract_Object_Name (Obj)));
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
         return Prefix (T, WNE_Type);
      end if;
   end To_Why_Type;

   --------
   -- Up --
   --------

   function Up (WT : W_Base_Type_Id) return W_Base_Type_Id is
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

   function Up (From, To : W_Base_Type_Id) return W_Base_Type_Id is
   begin
      if Eq (From, To) then
         return From;
      else
         return Up (From);
      end if;
   end Up;

   ---------------------
   -- Why_File_Suffix --
   ---------------------

   function Why_File_Suffix (Kind : Why_File_Enum) return String
   is
   begin
      case Kind is
         when WF_Types_In_Spec =>
            return "__types_in_spec";
         when WF_Types_In_Body =>
            return "__types_in_body";
         when WF_Variables =>
            return "__variables";
         when WF_Context_In_Spec =>
            return "__context_in_spec";
         when WF_Context_In_Body =>
            return "__context_in_body";
         when WF_Main =>
            return "__package";
      end case;
   end Why_File_Suffix;

begin
   Type_Hierarchy.Move_Child (EW_Unit, EW_Real);
   Type_Hierarchy.Move_Child (EW_Int, EW_Bool);
   Type_Hierarchy.Move_Child (EW_Real, EW_Int);
   Type_Hierarchy.Freeze;
end Why.Inter;
