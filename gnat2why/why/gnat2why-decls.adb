------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                         G N A T 2 W H Y - D E C L S                      --
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

with GNAT.Source_Info;

with Atree;               use Atree;
with Einfo;               use Einfo;
with Namet;               use Namet;
with Nlists;              use Nlists;
with Sem_Ch12;            use Sem_Ch12;
with Sem_Util;            use Sem_Util;
with Sinfo;               use Sinfo;
with Sinput;              use Sinput;
with String_Utils;        use String_Utils;

with SPARK_Definition;    use SPARK_Definition;
with SPARK_Util;          use SPARK_Util;

with Why.Ids;             use Why.Ids;
with Why.Sinfo;           use Why.Sinfo;
with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Mutators;  use Why.Atree.Mutators;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Binders;     use Why.Gen.Binders;
with Why.Gen.Expr;        use Why.Gen.Expr;
with Why.Inter;           use Why.Inter;
with Why.Types;           use Why.Types;
with Why.Conversions;     use Why.Conversions;

with Gnat2Why.Expr;       use Gnat2Why.Expr;
with Gnat2Why.Nodes;      use Gnat2Why.Nodes;

with Ada.Containers.Doubly_Linked_Lists;

package body Gnat2Why.Decls is

   package List_Of_Entity is new
     Ada.Containers.Doubly_Linked_Lists (Entity_Id);

   function Get_Generic_Parents (E : Entity_Id) return List_Of_Entity.List;
   --  Returns the list of every instance of generic package up to the first
   --  package with external axioms

   procedure Register_External_Entities (E : Entity_Id);
   --  This function is called on a package with external axioms.
   --  It registers all entities in the global symbol table.

   -----------------------------------
   -- Complete_Constant_Translation --
   -----------------------------------

   procedure Complete_Constant_Translation
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Base_Name : constant String := Full_Name (E);
      Name      : constant String :=
        Base_Name & To_String (WNE_Constant_Closure);

   begin
      Open_Theory (File, Name,
                   Comment =>
                     "Module including all necessary axioms for the "
                   & "constant "
                   & """" & Get_Name_String (Chars (E)) & """"
                   & (if Sloc (E) > 0 then
                        " declared at " & Build_Location_String (Sloc (E))
                     else "")
                   & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  No filtering is necessary here, as the theory should on the contrary
      --  use the previously defined theory for the constant.
      --  Attach the newly created theory as a completion of the existing one.

      Close_Theory (File,
                    Filter_Entity  => Empty,
                    Defined_Entity => E,
                    Do_Closure     => True);
      Add_Completion (Base_Name, Name, File.Kind);
   end Complete_Constant_Translation;

   -------------------------------------------------------
   -- Complete_Package_With_External_Axioms_Translation --
   -------------------------------------------------------

   procedure Complete_Package_With_External_Axioms_Translation
     (E    : Entity_Id)
   is

      procedure Compute_Completions
        (G_Parents :     List_Of_Entity.List;
         Compl     : out List_Of_Entity.List);
      --  Returns the list of the actuals of the generic parameters of
      --  G_Parents.

      procedure Complete_Decls (Decls  : List_Id;
                                C_List : List_Of_Entity.List);
      --  Generate an empty completion package for functions and constants
      --  Containing a reference to actuals of the generic parameters

      --  ??? Should be replaced by an import of the actuals of the generic
      --  parameters for every function that uses elements of the generic
      --  when the completion mechanism is redesigned.

      procedure Compute_Completions
        (G_Parents :     List_Of_Entity.List;
         Compl     : out List_Of_Entity.List) is

         procedure Compute_Completions_Package
           (Assoc         : List_Id);

         procedure Compute_Completions_Package
           (Assoc         : List_Id) is

            CurAssoc  : Node_Id := First (Assoc);
         begin
            while Present (CurAssoc) loop
               declare
                  Actual : constant Entity_Id :=
                    Entity (Explicit_Generic_Actual_Parameter (CurAssoc));
               begin
                  if not (Ekind (Actual) in Type_Kind) then
                     List_Of_Entity.Append (Compl, Actual);
                  end if;
               end;
               Next (CurAssoc);
            end loop;
         end Compute_Completions_Package;

         GParent_Cur : List_Of_Entity.Cursor :=
           List_Of_Entity.First (G_Parents);
      begin
         while List_Of_Entity.Has_Element (GParent_Cur) loop
            Compute_Completions_Package
              (Generic_Associations (Get_Package_Instantiation_Node
               (List_Of_Entity.Element (GParent_Cur))));

            List_Of_Entity.Next (GParent_Cur);
         end loop;
      end Compute_Completions;

      procedure Complete_Decls (Decls  : List_Id;
                                C_List : List_Of_Entity.List) is
         N      : Node_Id := First (Decls);
      begin

         while Present (N) loop
            if Comes_From_Source (N) and then
              Nkind (N) in N_Subtype_Declaration
              | N_Private_Type_Declaration
                | N_Subprogram_Declaration | N_Object_Declaration then
               declare
                  E : constant Entity_Id := Defining_Entity (N);
                  Theory_Name : constant String := Full_Name (E);
                  TFile : Why_Section :=  Why_Sections (Dispatch_Entity (E));
                  Completion : List_Of_Entity.Cursor :=
                    List_Of_Entity.First (C_List);
               begin

                  --  For constants, add a new empty theory for
                  --  constant_closure

                  if (Ekind (E) in Object_Kind
                      and then not Is_Mutable_In_Why (E))
                    or else Ekind (E) in Named_Kind then

                     Open_Theory
                       (TFile, Theory_Name & To_String (WNE_Constant_Closure),
                        Comment =>
                          "Module including all necessary axioms for the "
                        & "parameters of the generic constant "
                        & """" & Get_Name_String (Chars (E)) & """"
                        & (if Sloc (E) > 0 then
                             " declared at " & Build_Location_String (Sloc (E))
                          else "")
                        & ", created in " & GNAT.Source_Info.Enclosing_Entity);

                     --  Add the completion of function parameters

                     while List_Of_Entity.Has_Element (Completion) loop
                        Add_Use_For_Entity
                          (P               => TFile,
                           N               =>
                             List_Of_Entity.Element (Completion),
                           Use_Kind        => EW_Clone_Default,
                           With_Completion => True);

                        List_Of_Entity.Next (Completion);
                     end loop;

                     Close_Theory (TFile,
                                   Filter_Entity  => Empty,
                                   Defined_Entity => Empty,
                                   Do_Closure     => True);

                     Add_Completion
                       (Theory_Name,
                        Theory_Name & To_String (WNE_Constant_Closure),
                        TFile.Kind);
                  end if;

                  --  For subprograms, add a new empty theory for
                  --  expr_fun_closure

                  if Ekind (E) in Subprogram_Kind then
                     Open_Theory
                       (TFile, Theory_Name & To_String (WNE_Expr_Fun_Closure),
                        Comment =>
                          "Module including all necessary axioms for the "
                        & "parameters of the generic subprogram "
                        & """" & Get_Name_String (Chars (E)) & """"
                        & (if Sloc (E) > 0 then
                             " declared at " & Build_Location_String (Sloc (E))
                          else "")
                        & ", created in " & GNAT.Source_Info.Enclosing_Entity);

                     --  Add the completion of function parameters

                     while List_Of_Entity.Has_Element (Completion) loop
                        Add_Use_For_Entity
                          (P               => TFile,
                           N               =>
                             List_Of_Entity.Element (Completion),
                           Use_Kind        => EW_Clone_Default,
                           With_Completion => True);

                        List_Of_Entity.Next (Completion);
                     end loop;

                     Close_Theory (TFile,
                                   Filter_Entity  => Empty,
                                   Defined_Entity => Empty,
                                   Do_Closure     => True);

                     Add_Completion
                       (Theory_Name,
                        Theory_Name & To_String (WNE_Expr_Fun_Closure),
                        TFile.Kind);
                  end if;
               end;
            end if;

            --  Call Complete_Decls recursively on Package_Declaration and
            --  Package_Instantiation.

            if Comes_From_Source (N) and then
              Nkind (N) = N_Package_Instantiation then
               Complete_Decls
                 (Decls  => Visible_Declarations
                    (Specification (Instance_Spec (N))),
                  C_List => C_List);
            end if;

            if Comes_From_Source (N) and then
              Nkind (N) in N_Package_Declaration then
               Complete_Decls
                 (Decls  => Visible_Declarations (Get_Package_Spec (N)),
                  C_List => C_List);
            end if;

            Next (N);
         end loop;
      end Complete_Decls;

      C_List : List_Of_Entity.List;
   begin
      Compute_Completions (Get_Generic_Parents (E), C_List);

      Complete_Decls
        (Decls  => Visible_Declarations (Get_Package_Spec (E)),
         C_List => C_List);
   end Complete_Package_With_External_Axioms_Translation;

   -------------------------
   -- Get_Generic_Parents --
   -------------------------

   function Get_Generic_Parents
     (E : Entity_Id) return List_Of_Entity.List is

      procedure Internal_Get_Generic_Parents
        (E      :     Entity_Id;
         Result : out List_Of_Entity.List;
         Found  : out Boolean);

      procedure Internal_Get_Generic_Parents
        (E      :     Entity_Id;
         Result : out List_Of_Entity.List;
         Found  : out Boolean) is
      begin
         if Present (E) then

            --  If E has external axioms, return the empty list
            if Ekind (E) = E_Package and then
              Package_Has_External_Axioms (E) then
               Result := List_Of_Entity.Empty_List;
               Found := True;
               if Present (Generic_Parent (Get_Package_Spec (E))) then
                  List_Of_Entity.Prepend (Result, E);
               end if;
               return;
            end if;

            --  If a package with external axioms has been found above
            --  Scope (E) return the list of generic parents above Scope (E)
            Internal_Get_Generic_Parents (Scope (E), Result, Found);

            if Found then
               return;
            end if;

            --  If a package with external axioms has been found above
            --  Generic_Parent (E) return the list of generic parents above
            --  Generic_Parent (E) plus E

            if Ekind (E) = E_Package then
               Internal_Get_Generic_Parents
                 (Generic_Parent (Get_Package_Spec (E)), Result, Found);
               if Found then
                  List_Of_Entity.Prepend (Result, E);
                  return;
               end if;
            end if;
         end if;
         Found := False;
      end Internal_Get_Generic_Parents;

      Result : List_Of_Entity.List;
      Found  : Boolean;
   begin
      Internal_Get_Generic_Parents (E, Result, Found);
      pragma Assert (Found);
      return Result;
   end Get_Generic_Parents;

   --------------------------------
   -- Register_External_Entities --
   --------------------------------

   procedure Register_External_Entities (E : Entity_Id)
   is

      procedure Register_Decls (Decls  : List_Id);
      --  Register the entities of the declarations

      procedure Register_Decls (Decls  : List_Id) is
         N      : Node_Id := First (Decls);
      begin

         while Present (N) loop
            if Comes_From_Source (N) and then
              Nkind (N) in
              N_Subprogram_Declaration | N_Object_Declaration then
               declare
                  E : constant Entity_Id := Defining_Entity (N);
               begin
                  Ada_Ent_To_Why.Insert
                    (Symbol_Table,
                     E,
                     Binder_Type'(Ada_Node => E,
                                  B_Name   => To_Why_Id (E),
                                  B_Ent    => null,
                                  B_Type   => EW_Abstract (Etype (E)),
                                  Mutable  =>
                                    Ekind (E) in Object_Kind and then
                                  Is_Mutable_In_Why (E)));
               end;
            end if;

            --  Call Complete_Decls recursively on Package_Declaration and
            --  Package_Instantiation.

            if Comes_From_Source (N) and then
              Nkind (N) = N_Package_Instantiation then
               Register_Decls
                 (Decls  => Visible_Declarations
                    (Specification (Instance_Spec (N))));
            end if;

            if Comes_From_Source (N) and then
              Nkind (N) in N_Package_Declaration then
               Register_Decls
                 (Decls  => Visible_Declarations (Get_Package_Spec (N)));
            end if;

            Next (N);
         end loop;
      end Register_Decls;

   begin
      Register_Decls
        (Decls  => Visible_Declarations (Get_Package_Spec (E)));
   end Register_External_Entities;

   ------------------------
   -- Translate_Variable --
   ------------------------

   procedure Translate_Variable
     (File : in out Why_Section;
      E     : Entity_Id)
   is
      Name : constant String := Full_Name (E);
      Decl : constant W_Declaration_Id :=
        (if Entity_In_SPARK (E) then
            New_Type_Decl
              (Name  => To_Ident (WNE_Type),
               Alias => EW_Abstract (Etype (E)))
         else
            New_Type_Decl
              (Name => To_Ident (WNE_Type)));
      Typ  : constant W_Type_Id :=
        (if Ekind (E) = E_Loop_Parameter
         then EW_Int_Type
         else New_Named_Type (Name => Get_Name (W_Type_Decl_Id (Decl))));

      function Normalize_Type (E : Entity_Id) return Entity_Id;
      --  Choose the correct type to use

      --------------------
      -- Normalize_Type --
      --------------------

      function Normalize_Type (E : Entity_Id) return Entity_Id is
      begin
         if not (Ekind (E) in Private_Kind) or else
           Entity_In_External_Axioms (E)
         then
            return E;
         end if;
         if Entity_In_SPARK (MUT (E)) then
            return Normalize_Type (MUT (E));
         end if;
         return E;
      end Normalize_Type;

   begin
      Open_Theory (File, Name,
                   Comment =>
                     "Module for defining a ref holding the value of variable "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  Generate an alias for the name of the object's type, based on the
      --  name of the object. This is useful when generating logic functions
      --  from Ada functions, to generate additional parameters for the global
      --  objects read.

      Emit (File.Cur_Theory, Decl);

      if Entity_In_SPARK (MUT (Etype (E))) then
         Add_Use_For_Entity (File, Normalize_Type (Etype (E)));
      end if;

      --  We generate a global ref

      Emit
        (File.Cur_Theory,
         New_Global_Ref_Declaration
           (Name     => To_Why_Id (E, Local => True),
            Ref_Type => Typ));
      Ada_Ent_To_Why.Insert (Symbol_Table,
                             E,
                             Binder_Type'(
                               Ada_Node => E,
                               B_Name   => To_Why_Id (E),
                               B_Ent    => null,
                               B_Type   => Typ,
                               Mutable  => True));
      Close_Theory (File, Filter_Entity => E, No_Import => True);
   end Translate_Variable;

   ------------------------
   -- Translate_Constant --
   ------------------------

   procedure Translate_Constant
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Base_Name : constant String := Full_Name (E);
      Name      : constant String := Base_Name;
      Typ       : constant W_Type_Id := EW_Abstract (Etype (E));

   begin
      --  Start with opening the theory to define, as the creation of a
      --  function for the logic term needs the current theory to insert an
      --  include declaration.

      Open_Theory (File, Name,
                   Comment =>
                     "Module for defining the constant "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  We generate a "logic", whose axiom will be given in a completion

      Emit (File.Cur_Theory,
            Why.Atree.Builders.New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Why_Id (E, Domain => EW_Term, Local => True),
               Binders     => (1 .. 0 => <>),
               Return_Type => Typ));
      Ada_Ent_To_Why.Insert (Symbol_Table,
                             E,
                             Binder_Type'(
                               Ada_Node => E,
                               B_Name   => To_Why_Id (E),
                               B_Ent    => null,
                               B_Type   => Typ,
                               Mutable  => False));
      Close_Theory (File,
                    Filter_Entity  => E,
                    Defined_Entity => E);
   end Translate_Constant;

   ------------------------------
   -- Translate_Constant_Value --
   ------------------------------

   procedure Translate_Constant_Value
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Base_Name : constant String := Full_Name (E);
      Name      : constant String :=
        Base_Name & To_String (WNE_Constant_Axiom);
      Typ    : constant W_Type_Id := EW_Abstract (Etype (E));
      Decl   : constant Node_Id := Parent (E);
      Def    : W_Term_Id;

      --  Always use the Ada type for the equality between the constant result
      --  and the translation of its initialization expression. Using "int"
      --  instead is tempting to facilitate the job of automatic provers, but
      --  it is potentially incorrect. For example for:

      --    C : constant Natural := Largest_Int + 1;

      --  we should *not* generate the incorrect axiom:

      --    axiom c__def:
      --      to_int(c) = to_int(largest_int) + 1

      --  but the correct one:

      --    axiom c__def:
      --      c = of_int (to_int(largest_int) + 1)

      Use_Ty : constant W_Type_Id := Type_Of_Node (E);

   begin
      --  Start with opening the theory to define, as the creation of a
      --  function for the logic term needs the current theory to insert an
      --  include declaration.

      Open_Theory (File, Name,
                   Comment =>
                     "Module for defining the value of constant "
                       & """" & Get_Name_String (Chars (E)) & """"
                       & (if Sloc (E) > 0 then
                            " defined at " & Build_Location_String (Sloc (E))
                          else "")
                       & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  Default values of parameters are not considered as the value of the
      --  constant representing the parameter.

      if Ekind (E) /= E_In_Parameter
        and then Present (Expression (Decl))
      then
         Def := Get_Pure_Logic_Term_If_Possible
           (File, Expression (Decl), Use_Ty);
      else
         Def := Why_Empty;
      end if;

      if Def = Why_Empty then
         Discard_Theory (File);

      else
         --  The definition of constants is done in a separate theory. This
         --  theory is added as a completion of the base theory defining the
         --  constant.

         if Is_Full_View (E) then

            --  It may be the case that the full view has a more precise type
            --  than the partial view, for example when the type of the partial
            --  view is an indefinite array. In that case, convert back to the
            --  expected type for the constant.

            if Etype (Partial_View (E)) /= Etype (E) then
               Def := W_Term_Id (Insert_Simple_Conversion
                        (Domain   => EW_Term,
                         Ada_Node => Expression (Decl),
                         Expr     => W_Expr_Id (Def),
                         From     => Use_Ty,
                         To       => Type_Of_Node (Partial_View (E))));
            end if;

            Emit
              (File.Cur_Theory,
               New_Defining_Axiom
                 (Name        =>
                    To_Why_Id (E, Domain => EW_Term, Local => False),
                  Return_Type => Get_EW_Type (Typ),
                  Binders     => (1 .. 0 => <>),
                  Def         => Def));

            --  No filtering is necessary here, as the theory should on the
            --  contrary use the previously defined theory for the partial
            --  view. Attach the newly created theory as a completion of the
            --  existing one.

            Close_Theory (File,
                          Filter_Entity  => Empty,
                          Defined_Entity => Partial_View (E));
            Add_Completion (Base_Name, Name, File.Kind);

         --  In the general case, we generate a defining axiom if necessary and
         --  possible.

         else
            Emit
              (File.Cur_Theory,
               New_Defining_Axiom
                 (Name        =>
                    To_Why_Id (E, Domain => EW_Term, Local => False),
                  Return_Type => Get_EW_Type (Typ),
                  Binders     => (1 .. 0 => <>),
                  Def         => Def));

            --  No filtering is necessary here, as the theory should on the
            --  contrary use the previously defined theory for the partial
            --  view.

            Close_Theory (File,
                          Filter_Entity  => Empty,
                          Defined_Entity => E);
            Add_Completion (Base_Name, Name, File.Kind);
         end if;
      end if;
   end Translate_Constant_Value;

   --------------------------------------------
   -- Translate_Package_With_External_Axioms --
   --------------------------------------------

   procedure Translate_Package_With_External_Axioms
     (Package_Entity : Entity_Id)
   is
      procedure Compute_Length (G_Parents    :     List_Of_Entity.List;
                                Subst_Length : out Natural);
      --  Computes the length of the substitution that has to be computed
      --  for the parameters of the generic.

      procedure Compute_Substitution
        (G_Parents :     List_Of_Entity.List;
         Subst     : out W_Custom_Substitution_Array);
      --  Creates a substitution for the generic parameters of the package
      --  if any. The substitution is a string following the format in
      --  GNAT.Regpat. It is then used to copy the associated Why3
      --  axiomatization.

      function Get_Association_List (E : Entity_Id) return List_Id is
         (Generic_Associations (Get_Package_Instantiation_Node (E)));

      function Get_Generic_Name (E : Entity_Id;
                                 Parents : List_Of_Entity.Cursor)
                                 return String;
      --  Returns the sequence of every scope of E where instances are replaced
      --  by generics.
      --  E should be an element of the path between Package_Entity and the
      --  first package with external axioms above it

      function Get_Instance_Name (E : Entity_Id) return String is
        (Capitalize_First (Full_Name (E)));

      function Get_Label_List (E : Entity_Id) return List_Id;
      --  Use Parent field to reach N_Generic_Package_Declaration

      procedure Parse_Parameters (G_Parents : List_Of_Entity.List);
      --  Declares a Why type per formal of type kind of the first element of
      --  G_Parents and a Why function per formal of function kind of the first
      --  element of G_Parents

      --------------------
      -- Compute_Length --
      --------------------

      procedure Compute_Length (G_Parents    :     List_Of_Entity.List;
                                Subst_Length : out Natural) is

         procedure Compute_Length_Package (Labs         :     List_Id;
                                           Subst_Length : in out Natural);

         procedure Compute_Length_Package (Labs         :     List_Id;
                                           Subst_Length : in out Natural) is
            CurLabs  : Node_Id := First (Labs);
         begin
            Subst_Length := Subst_Length + 2;
            while Present (CurLabs) loop
               declare
                  K : constant Entity_Kind :=
                    Ekind (Defining_Entity (CurLabs));
               begin
                  if K in Private_Kind then
                     Subst_Length := Subst_Length + 6;
                  elsif K in Type_Kind then
                     Subst_Length := Subst_Length + 3;
                  else
                     Subst_Length := Subst_Length + 2;
                  end if;
               end;
               Next (CurLabs);
            end loop;
         end Compute_Length_Package;

         CurGParent : List_Of_Entity.Cursor :=
           List_Of_Entity.First (G_Parents);
      begin
         Subst_Length := 0;

         while List_Of_Entity.Has_Element (CurGParent) loop
            Compute_Length_Package (Get_Label_List
                                    (List_Of_Entity.Element (CurGParent)),
                                    Subst_Length);
            List_Of_Entity.Next (CurGParent);
         end loop;
      end Compute_Length;

      --------------------------
      -- Compute_Substitution --
      --------------------------

      procedure Compute_Substitution
        (G_Parents     :     List_Of_Entity.List;
         Subst         : out W_Custom_Substitution_Array) is

         procedure Compute_Substitution_Package
           (Assoc         : List_Id;
            Labs          : List_Id;
            Generic_Name  : String;
            Instance_Name : String);

         --  Names of elements expected in a Why3 theory for a formal of a
         --  private type. Used to comply with the special handling for
         --  range types. In parameters of subprograms are expected to be of
         --  type Base_Type_Name. The functions To_Base_Name and Of_Base_Name
         --  are used to translate to and from type Base_Type_Name and
         --  the predicate In_Range_Name asserts that an element of type
         --  Base_Type_Name can be translated back to the range type.

         Base_Type_Name : constant String := "base_type";
         To_Base_Name   : constant String := "to_base";
         Of_Base_Name   : constant String := "of_base";
         In_Range_Name  : constant String := "valid";
         Subst_Cur : Integer := 1;

         procedure Compute_Substitution_Package
           (Assoc         : List_Id;
            Labs          : List_Id;
            Generic_Name  : String;
            Instance_Name : String) is

            CurAssoc  : Node_Id := First (Assoc);
            CurLabs   : Node_Id := First (Labs);
         begin
            while Present (CurAssoc) loop
               declare
                  Actual : constant Entity_Id :=
                    Entity (Explicit_Generic_Actual_Parameter (CurAssoc));
                  Formal : constant Entity_Id := Defining_Entity (CurLabs);
               begin

                  if Ekind (Formal) in Type_Kind then

                     --  Replace:
                     --  use "<Generic_Name>__args".<Generic_Name>__<Formal>
                     --  by: use ("<Actual_File>".)Name_Of_Node (Actual)
                     --  No use is generated if Actual doesn't have a unique
                     --  name

                     if Full_Name_Is_Not_Unique_Name (Actual) then
                        Subst (Subst_Cur) := New_Custom_Substitution
                          (Domain   => EW_Prog,
                           From     => NID ("use\s+" & """" & Generic_Name &
                               "__args""\." & Capitalize_First (Generic_Name)
                             & "__" & Short_Name (Formal) & "\s"),
                           To       => W_Any_Node_Id (
                             New_Identifier (Name => "" & ASCII.LF)));
                     else
                        Subst (Subst_Cur) := New_Custom_Substitution
                          (Domain   => EW_Prog,
                           From     => NID ("use\s+" & """" & Generic_Name &
                               "__args""\." & Capitalize_First (Generic_Name)
                             & "__" & Short_Name (Formal) & "\s"),
                           To       => W_Any_Node_Id (New_Identifier
                             (Name => "use " & Capitalize_First
                              (Name_Of_Node (Actual)) & ASCII.LF)));
                     end if;
                     Subst_Cur := Subst_Cur + 1;

                     --  Replace: <Generic_Name>__<Formal>.<Formal>
                     --  by: Why_Logic_Type_Of_Ada_Type (Actual)

                     Subst (Subst_Cur) := New_Custom_Substitution
                       (Domain   => EW_Prog,
                        From     => NID (Capitalize_First (Generic_Name)
                          & "__" & Short_Name (Formal) & "\." &
                            Short_Name (Formal)),
                        To       => W_Any_Node_Id
                          (EW_Abstract (Actual)));

                     --  If the formal has a private kind, Base_Type_Name,
                     --  To_Base_Name, Of_Base_Name, and In_Range_Name must be
                     --  replaced appropriately

                     if Ekind (Formal) in Private_Kind then
                        declare
                           Actual_Type : constant W_Type_OId :=
                             EW_Abstract (Actual);
                           Actual_Base : constant W_Type_OId :=
                             +Base_Why_Type (Unique_Entity (Actual));
                        begin

                           --  If the actual is a scalar type and not a bool:
                           --  <Generic_Name>__<Base_Type_Name> =>
                           --               Base_Why_Type (<Actual>)
                           --  <Generic_Name>__<To_Base_Name>   =>
                           --               Conversion_Name (To   => <Base>,
                           --                                From => <Actual>)
                           --  <Generic_Name>__<Of_Base_Name>   =>
                           --               Conversion_Name (From => <Base>,
                           --                                To   => <Actual>)
                           --  <Generic_Name>__<In_Range_Name>  =>
                           --               Range_Pred_Name (<Actual>)
                           --  Otherwise:
                           --  <Generic_Name>__<Base_Type_Name> => <Actual>
                           --  <Generic_Name>__<To_Base_Name>   =>
                           --  <Generic_Name>__<Of_Base_Name>   =>
                           --  <Generic_Name>__<In_Range_Name>  => __ignore

                           if Is_Scalar_Type (Actual) and then
                             not Is_Boolean_Type (Actual) then
                              Subst (Subst_Cur + 1) := New_Custom_Substitution
                                (Domain   => EW_Prog,
                                 From     => NID (Capitalize_First
                                   (Generic_Name)  & "__" & Short_Name (Formal)
                                   & "\." & Base_Type_Name),
                                 To       => W_Any_Node_Id (Actual_Base));

                              Subst (Subst_Cur + 2) := New_Custom_Substitution
                                (Domain   => EW_Prog,
                                 From     => NID (Capitalize_First
                                   (Generic_Name) & "__" & Short_Name (Formal)
                                   & "\." & To_Base_Name),
                                 To       => W_Any_Node_Id (Conversion_Name
                                   (From => +Actual_Type,
                                    To => +Actual_Base)));

                              Subst (Subst_Cur + 3) := New_Custom_Substitution
                                (Domain   => EW_Prog,
                                 From     => NID (Capitalize_First
                                   (Generic_Name) & "__" & Short_Name (Formal)
                                   & "\." & Of_Base_Name),
                                 To       => W_Any_Node_Id (Conversion_Name
                                   (From => +Actual_Base,
                                    To => +Actual_Type)));

                              Subst (Subst_Cur + 4) := New_Custom_Substitution
                                (Domain   => EW_Prog,
                                 From     => NID (Capitalize_First
                                   (Generic_Name) & "__" & Short_Name (Formal)
                                   & "\." & In_Range_Name),
                                 To       => W_Any_Node_Id
                                   (Range_Pred_Name (Actual)));
                           else
                              Subst (Subst_Cur + 1) := New_Custom_Substitution
                                (Domain   => EW_Prog,
                                 From     => NID (Capitalize_First
                                   (Generic_Name) & "__" & Short_Name (Formal)
                                   & "\." & Base_Type_Name),
                                 To       => W_Any_Node_Id (Actual_Type));

                              Subst (Subst_Cur + 2) := New_Custom_Substitution
                                (Domain   => EW_Prog,
                                 From     => NID (Capitalize_First
                                   (Generic_Name) & "__" & Short_Name (Formal)
                                   & "\." & To_Base_Name),
                                 To       => W_Any_Node_Id
                                   (New_Identifier (Name => "")));

                              Subst (Subst_Cur + 3) := New_Custom_Substitution
                                (Domain   => EW_Prog,
                                 From     => NID (Capitalize_First
                                   (Generic_Name) & "__" & Short_Name (Formal)
                                   & "\." & Of_Base_Name),
                                 To       => W_Any_Node_Id
                                   (New_Identifier (Name => "")));

                              Subst (Subst_Cur + 4) := New_Custom_Substitution
                                (Domain   => EW_Prog,
                                 From     => NID (Capitalize_First
                                   (Generic_Name) & "__" & Short_Name (Formal)
                                   & "\." & In_Range_Name),
                                 To       => W_Any_Node_Id
                                   (New_Identifier (Name => "__ignore")));
                           end if;
                        end;
                        Subst_Cur := Subst_Cur + 5;
                     else

                        --  If the formal is not of a private kind, there can
                        --  be some other elements in its module that are used
                        --  inside the axiomatization.
                        --  Replace: <Generic_Name>__<Formal>.
                        --  by: Name_Of_Node (Actual).

                        Subst (Subst_Cur + 1) := New_Custom_Substitution
                          (Domain   => EW_Prog,
                           From     => NID (Capitalize_First (Generic_Name)
                             & "__" & Short_Name (Formal) & "\."),
                           To       => W_Any_Node_Id
                             (New_Identifier (Name => Capitalize_First
                                              (Name_Of_Node (Actual)) & ".")));
                        Subst_Cur := Subst_Cur + 2;
                     end if;

                  elsif Ekind (Formal) = E_Function then

                     --  Replace:
                     --  use "<Generic_Name>__args".<Generic_Name>__<Formal>
                     --  by: use <Instance_Name>__<Formal>

                     Subst (Subst_Cur) := New_Custom_Substitution
                       (Domain   => EW_Prog,
                        From     => NID ("use\s+" & """" & Generic_Name &
                            "__args""\." & Capitalize_First (Generic_Name)
                          & "__" & Short_Name (Formal) & "\s"),
                        To       => W_Any_Node_Id (New_Identifier
                          (Name => "use " & Capitalize_First (Instance_Name)
                           & "__" & Short_Name (Formal) & ASCII.LF)));
                     Subst_Cur := Subst_Cur + 1;

                     --  Replace: <Generic_Name>__<Formal>.<Formal>
                     --  by: <Instance_Name>__<Formal>.<Formal>

                     Subst (Subst_Cur) := New_Custom_Substitution
                       (Domain   => EW_Prog,
                        From     => NID (Capitalize_First (Generic_Name)
                          & "__" & Short_Name (Formal) & "\." &
                            Short_Name (Formal)),
                        To       => W_Any_Node_Id
                          (New_Identifier
                               (Name => Short_Name (Formal),
                                Context =>
                                  Capitalize_First (Instance_Name) & "__"
                                & Short_Name (Formal))));
                     Subst_Cur := Subst_Cur + 1;

                  else

                     --  Replace:
                     --  use "<Generic_Name>__args".<Generic_Name>__<Formal>
                     --  by: use Name_Of_Node (Actual)

                     Subst (Subst_Cur) := New_Custom_Substitution
                       (Domain   => EW_Prog,
                        From     => NID ("use\s+" & """" & Generic_Name &
                            "__args""\." & Capitalize_First (Generic_Name)
                          & "__" & Short_Name (Formal) & "\s"),
                        To       => W_Any_Node_Id (New_Identifier
                          (Name => "use " & Capitalize_First
                           (Name_Of_Node (Actual)) & ASCII.LF)));
                     Subst_Cur := Subst_Cur + 1;

                     --  Replace: <Generic_Name>__<Formal>.<Formal>
                     --  by: To_Why_Id (Actual)

                     Subst (Subst_Cur) := New_Custom_Substitution
                       (Domain   => EW_Prog,
                        From     => NID (Capitalize_First (Generic_Name)
                          & "__" & Short_Name (Formal) & "\." &
                            Short_Name (Formal)),
                        To       => W_Any_Node_Id
                          (To_Why_Id (Actual, Domain => EW_Term)));
                     Subst_Cur := Subst_Cur + 1;
                  end if;
               end;
               Next (CurAssoc);
               Next (CurLabs);
            end loop;

            --  Rename every module in the copy.
            --  Replace: <Generic_Name>__ by: <Instance_Name>__

            Subst (Subst_Cur) := New_Custom_Substitution
              (Domain   => EW_Prog,
               From     => NID (Capitalize_First (Generic_Name) & "__"),
               To       => W_Any_Node_Id
                 (New_Identifier (Name => Instance_Name & "__")));

            Subst_Cur := Subst_Cur + 1;

            --  Rename the theory file.
            --  Replace: "<Generic_Name>". by:
            --    "<Instance_File>". if Instance_File is not File_Name
            --    nothing otherwise

            Subst (Subst_Cur) := New_Custom_Substitution
              (Domain   => EW_Prog,
               From     => NID ("""" & Generic_Name & """."),
               To       => W_Any_Node_Id
                 (New_Identifier (Name => "")));

            Subst_Cur := Subst_Cur + 1;
         end Compute_Substitution_Package;

         GParent_Cur : List_Of_Entity.Cursor :=
           List_Of_Entity.First (G_Parents);

      begin
         while List_Of_Entity.Has_Element (GParent_Cur) loop
            declare
               E             : constant Entity_Id :=
                 List_Of_Entity.Element (GParent_Cur);
               Assoc         : constant List_Id := Get_Association_List (E);
               Labs          : constant List_Id := Get_Label_List (E);
               Generic_Name  : constant String  :=
                 Get_Generic_Name (E, GParent_Cur);
               Instance_Name : constant String  := Get_Instance_Name (E);
            begin

               Compute_Substitution_Package
                 (Assoc         => Assoc,
                  Labs          => Labs,
                  Generic_Name  => Generic_Name,
                  Instance_Name => Instance_Name);

               List_Of_Entity.Next (GParent_Cur);

            end;
         end loop;
      end Compute_Substitution;

      ----------------------
      -- Get_Generic_Name --
      ----------------------

      function Get_Generic_Name
        (E : Entity_Id;
         Parents : List_Of_Entity.Cursor) return String
      is
         function Get_Generic_Name_Scope
           (E : Entity_Id; N : List_Of_Entity.Cursor) return String;
         --  ???

         function Get_Generic_Name_Scope
           (E : Entity_Id; N : List_Of_Entity.Cursor) return String is
         begin
            if List_Of_Entity.Has_Element (N) then

               --  If E is the next instance N, then use the name of its
               --  Generic_Parent instead.

               if List_Of_Entity.Element (N) = E then
                  return
                    Get_Generic_Name_Scope
                      (Generic_Parent (Get_Package_Spec (E)),
                       List_Of_Entity.Next (N));
               else

                  --  Append the name of E to its Scope

                  declare
                     Name : constant String := Get_Name_String (Chars (E));
                  begin
                     return Get_Generic_Name_Scope
                       (Unique_Entity (Scope (E)), N) & "__" & Name;
                  end;
               end if;
            else

               --  If there is no instance, return E's full name

               return Full_Name (E);
            end if;
         end Get_Generic_Name_Scope;
      begin
         return Get_Generic_Name_Scope (E, Parents);
      end Get_Generic_Name;

      --------------------
      -- Get_Label_List --
      --------------------

      function Get_Label_List (E : Entity_Id) return List_Id is
         P : Node_Id := Generic_Parent (Get_Package_Spec (E));
      begin
         while Nkind (P) /= N_Generic_Package_Declaration loop
            P := Parent (P);
         end loop;

         return Generic_Formal_Declarations (P);
      end Get_Label_List;

      ----------------------
      -- Parse_Parameters --
      ----------------------

      procedure Parse_Parameters (G_Parents : List_Of_Entity.List) is
         Assoc : constant List_Id :=  Get_Association_List (Package_Entity);
         Labs  : constant List_Id :=  Get_Label_List (Package_Entity);
         Instance_Name : constant String := Get_Instance_Name (Package_Entity);

         function Why_Logic_Type_Of_Ada_Generic_Type
           (Ty       : Node_Id;
            Is_Input : Boolean) return W_Type_Id;
         --  Take an Ada Node and transform it into a Why logic type. The Ada
         --  Node is expected to be a Defining_Identifier for a type.
         --  Return the associated actual if Ty is a generic formal parameter.
         --  If Is_Input is True then returns the base_type if base_type should
         --  be used.

         function Why_Logic_Type_Of_Ada_Generic_Type
           (Ty       : Node_Id;
            Is_Input : Boolean) return W_Type_Id is

            --  Goes through a list of parameters to find actual that is
            --  associated with the formal Ty
            function Find_Actual
              (Assoc : List_Id;
               Labs  : List_Id) return Node_Id;

            function Find_Actual
              (Assoc : List_Id;
               Labs  : List_Id) return Node_Id is

               CurAssoc   : Node_Id := First (Assoc);
               CurLabs    : Node_Id := First (Labs);
            begin
               while Present (CurAssoc) loop
                  if Defining_Entity (CurLabs) = Ty then
                     return Entity (Explicit_Generic_Actual_Parameter
                                    (CurAssoc));
                  end if;

                  Next (CurLabs);
                  Next (CurAssoc);
               end loop;
               return Empty;
            end Find_Actual;

         begin
            if Is_Generic_Type (Ty) then
               declare
                  Actual     : Node_Id := Find_Actual (Assoc, Labs);
                  CurGParent : List_Of_Entity.Cursor :=
                    List_Of_Entity.Next (List_Of_Entity.First (G_Parents));
               begin

                  --  If Ty is a formal of the generic, goes through the list
                  --  of enclosing instances to find the corresponding actual.

                  while List_Of_Entity.Has_Element (CurGParent) and then
                    not Present (Actual) loop
                     Actual := Find_Actual
                       (Assoc => Get_Association_List (
                        List_Of_Entity.Element (CurGParent)),
                        Labs  => Get_Label_List (
                          List_Of_Entity.Element (CurGParent)));

                     List_Of_Entity.Next (CurGParent);
                  end loop;

                  pragma Assert (Present (Actual));

                  --  If Is_Input is true, checks wether the base_type of
                  --  Ty should be used.

                  if Is_Input and then
                    Is_Scalar_Type (Actual) and then
                    not Is_Boolean_Type (Actual) then
                     return Base_Why_Type (Unique_Entity (Actual));
                  else
                     return EW_Abstract (Actual);
                  end if;
               end;
            else
               if Is_Input and then
                 Is_Scalar_Type (Ty) and then
                 not Is_Boolean_Type (Ty) then

                  --  If Is_Input is true, checks wether the base_type of
                  --  Ty should be used.

                  return Base_Why_Type (Unique_Entity (Ty));
               else
                  return EW_Abstract (Ty);
               end if;
            end if;
         end Why_Logic_Type_Of_Ada_Generic_Type;

         TFile     : Why_Section :=
           Why_Sections (Dispatch_Entity (Package_Entity));
         CurAssoc  : Node_Id := First (Assoc);
         CurLabs   : Node_Id := First (Labs);

      begin
         while Present (CurAssoc) loop
            declare
               Actual : constant Entity_Id :=
                 Entity (Explicit_Generic_Actual_Parameter (CurAssoc));
               Formal : constant Entity_Id := Defining_Entity (CurLabs);

            begin

               if Ekind (Formal) in Type_Kind and then
                 not Full_Name_Is_Not_Unique_Name (Formal) then

                  --  For type parameters, generate a theory that renames the
                  --  theory of the actual. Necessary for conversion functions.

                  Open_Theory
                    (TFile, Capitalize_First (Instance_Name) & "__"
                     & Short_Name (Formal),
                     Comment =>
                       "Module for declaring a why type for the formal "
                     & """" & Get_Name_String (Chars (Formal)) & """"
                     & (if Sloc (Formal) > 0 then
                          " defined at " &
                          Build_Location_String (Sloc (Formal))
                       else "")
                     & ", created in " & GNAT.Source_Info.Enclosing_Entity);

                  Add_Use_For_Entity
                    (P               => TFile,
                     N               => Actual,
                     Use_Kind        => EW_Export,
                     With_Completion => False);

                  if Short_Name (Formal) /= Short_Name (Actual) then
                     Emit
                       (TFile.Cur_Theory,
                        New_Type_Decl
                          (Name  =>
                               New_Identifier (Name => Short_Name (Formal)),
                           Alias => EW_Abstract (Actual)));
                  end if;

                  if Ekind (Actual) in E_Record_Type and then
                    Root_Record_Type (Actual) = Actual then

                     --  if the actual is a root type of a record type, we need
                     --  to define the conversion functions

                     declare
                        F_Ty   : constant W_Type_Id :=
                          +New_Named_Type
                            (Name => New_Identifier
                               (Name => Short_Name (Formal)));
                        A_Ident    : constant W_Identifier_Id :=
                          New_Identifier (Name => "a");
                        R_Binder   : constant Binder_Array :=
                          (1 => (B_Name => A_Ident,
                                 B_Type => F_Ty,
                                 others => <>));
                     begin

                        Emit
                          (TFile.Cur_Theory,
                           New_Function_Def
                             (Domain      => EW_Term,
                              Name        => To_Ident (WNE_To_Base),
                              Binders     => R_Binder,
                              Return_Type => F_Ty,
                              Def         => +A_Ident));
                        Emit
                          (TFile.Cur_Theory,
                           New_Function_Def
                             (Domain      => EW_Term,
                              Name        => To_Ident (WNE_Of_Base),
                              Binders     => R_Binder,
                              Return_Type => F_Ty,
                              Def         => +A_Ident));

                     end;
                  end if;

                  Close_Theory (TFile, Filter_Entity => Empty);

               elsif Ekind (Formal) = E_Function then

                  --  For function parameters, generate a new function
                  --  that introduced the needed conversions:
                  --  function <formal> "inline" (x1 : ty_formal_1, ...)
                  --                        : ty_formal =
                  --  <ty_actual__to__ty_formal> (<actual>
                  --      (<ty_formal1__to__ty_actual1> (x1)) ...)

                  Open_Theory
                    (TFile, Capitalize_First (Instance_Name) & "__"
                     & Short_Name (Formal),
                     Comment =>
                       "Module for declaring a logic function for the formal "
                     & """" & Get_Name_String (Chars (Formal)) & """"
                     & (if Sloc (Formal) > 0 then
                          " defined at " &
                          Build_Location_String (Sloc (Formal))
                       else "")
                     & ", created in " & GNAT.Source_Info.Enclosing_Entity);

                  Add_Use_For_Entity
                    (P               => TFile,
                     N               => Actual,
                     Use_Kind        => EW_Clone_Default,
                     With_Completion => False);

                  declare
                     F_Params : constant List_Id :=
                       Parameter_Specifications
                         (Get_Subprogram_Spec (Formal));
                     F_Param : Node_Id := First (F_Params);
                     F_Type : constant W_Type_Id :=
                       Why_Logic_Type_Of_Ada_Generic_Type
                         (Etype (Formal), False);
                     A_Params : constant List_Id :=
                       Parameter_Specifications
                         (Get_Subprogram_Spec (Actual));
                     A_Param : Node_Id := First (A_Params);
                     A_Type : constant W_Type_Id :=
                       EW_Abstract (Etype (Actual));
                     Binders : Binder_Array
                       (1 .. Integer (List_Length (F_Params)));
                     Args    : W_Expr_Array
                       (1 .. Integer (List_Length (F_Params)));
                     Count : Integer := 1;
                  begin

                     pragma Assert (List_Length (F_Params) =
                                      List_Length (A_Params));

                     while Present (F_Param) loop
                        declare
                           A_Id   : constant Node_Id :=
                             Defining_Identifier (A_Param);
                           A_Type : constant W_Type_Id :=
                             (if Use_Why_Base_Type (A_Id) then
                              +Base_Why_Type (Unique_Entity (Etype (A_Id)))
                              else EW_Abstract (Etype (A_Id)));
                           F_Id   : constant Node_Id :=
                             Defining_Identifier (F_Param);
                           F_Type : constant W_Type_Id :=
                             Why_Logic_Type_Of_Ada_Generic_Type
                               (Etype (F_Id), True);
                           Name : constant W_Identifier_Id :=
                             New_Identifier
                               (Ada_Node => Empty,
                                Name => Full_Name (F_Id));
                        begin
                           Binders (Count) :=
                             (Ada_Node => F_Id,
                              B_Name   => Name,
                              B_Ent    => null,
                              Mutable  => False,
                              B_Type   => F_Type);

                           Args (Count) := Insert_Simple_Conversion
                             (Domain        => EW_Term,
                              Expr          => +Name,
                              To            => +A_Type,
                              From          => +F_Type);

                           Next (F_Param);
                           Next (A_Param);
                           Count := Count + 1;
                        end;
                     end loop;

                     Emit
                       (TFile.Cur_Theory,
                        New_Function_Def
                          (Domain      => EW_Term,
                           Name        =>
                             New_Identifier (Name => Short_Name (Formal)),
                           Binders     => Binders,
                           Return_Type => F_Type,
                           Labels      =>
                             (1 => New_Identifier (Name => "inline")),
                           Def         =>
                             Insert_Simple_Conversion
                             (Domain        => EW_Term,
                              Expr          => New_Call
                                (Domain   => EW_Term,
                                 Name     => To_Why_Id (Actual,
                                   Domain => EW_Term),
                                 Args  => Args),
                              To            => +F_Type,
                              From          => +A_Type)));

                  end;

                  Close_Theory (TFile, Filter_Entity => Empty);

               end if;
            end;
            Next (CurAssoc);
            Next (CurLabs);
         end loop;
      end Parse_Parameters;

      TFile : constant Why_Section :=
        Why_Sections (Dispatch_Entity (Package_Entity));
      G_Parents : constant List_Of_Entity.List :=
        Get_Generic_Parents (Package_Entity);
      Subst_Length : Natural;

   begin
      Register_External_Entities (Package_Entity);
      if List_Of_Entity.Is_Empty (G_Parents) then
         File_Append_To_Theories
           (TFile.File, New_Custom_Declaration
              (Ada_Node  => Package_Entity,
               Domain    => EW_Prog,
               File_Name => NID (Full_Name (Package_Entity) & ".mlw")));
      else
         if List_Of_Entity.First_Element (G_Parents) = Package_Entity then
            Parse_Parameters (G_Parents);
         end if;

         Compute_Length (G_Parents, Subst_Length);

         declare
            Subst : W_Custom_Substitution_Array (1 .. Subst_Length);
         begin
            Compute_Substitution (G_Parents, Subst);

            File_Append_To_Theories
              (TFile.File, New_Custom_Declaration
                 (Domain    => EW_Prog,
                  File_Name =>
                    NID (Get_Generic_Name (Package_Entity,
                      List_Of_Entity.First (G_Parents)) & ".mlw"),
                  Subst     => Subst));

         end;
      end if;
   end Translate_Package_With_External_Axioms;

   -------------------------------
   -- Translate_External_Object --
   -------------------------------

   procedure Translate_External_Object (E : Entity_Name) is
      File : Why_Section := Why_Sections (WF_Variables);
   begin
      Open_Theory
        (File, Capitalize_First (E.all),
         Comment =>
           "Module declaring the external object """ & E.all &
           ","" created in " & GNAT.Source_Info.Enclosing_Entity);

      Add_With_Clause (File.Cur_Theory, "ref", "Ref", EW_Import, EW_Module);

      Emit (File.Cur_Theory,
            New_Type_Decl (Name => To_Ident (WNE_Type)));
      Emit
        (File.Cur_Theory,
         New_Global_Ref_Declaration
           (Name     => To_Why_Id (E.all, Local => True),
            Ref_Type => +New_Named_Type (Name => To_Ident (WNE_Type))));

      Close_Theory (File, Filter_Entity => Empty, No_Import => True);
   end Translate_External_Object;

   ---------------------------
   -- Translate_Loop_Entity --
   ---------------------------

   procedure Translate_Loop_Entity
     (File : in out Why_Section;
      E    : Entity_Id)
   is
      Name : constant String := Full_Name (E);
   begin
      Open_Theory (File, Name,
                   Comment =>
                     "Module for defining the loop exit exception for the loop"
                   & """" & Get_Name_String (Chars (E)) & """"
                   & (if Sloc (E) > 0 then
                     " defined at " & Build_Location_String (Sloc (E))
                     else "")
                   & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Emit (File.Cur_Theory,
            New_Exception_Declaration (Name => To_Why_Id (E, Local => True),
                                       Arg  => Why_Empty));

      Close_Theory (File, Filter_Entity => E, No_Import => True);
   end Translate_Loop_Entity;

   -----------------------
   -- Use_Why_Base_Type --
   -----------------------

   function Use_Why_Base_Type (E : Entity_Id) return Boolean
   is
      Ty : constant Entity_Id := Etype (E);
   begin
      return not Is_Mutable_In_Why (E) and then
        Is_Scalar_Type (Ty) and then
        not Is_Boolean_Type (Ty);
   end Use_Why_Base_Type;

end Gnat2Why.Decls;
