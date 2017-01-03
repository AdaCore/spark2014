------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              G N A T 2 W H Y - E X T E R N A L _ A X I O M S             --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2017, AdaCore                   --
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

with Ada.Containers.Doubly_Linked_Lists;
with Atree;                              use Atree;
with Common_Containers;                  use Common_Containers;
with Einfo;                              use Einfo;
with Errout;                             use Errout;
with Exp_Util;                           use Exp_Util;
with Flow_Utility;                       use Flow_Utility;
with GNAT.Source_Info;
with Gnat2Why.Expr;                      use Gnat2Why.Expr;
with Gnat2Why.Subprograms;               use Gnat2Why.Subprograms;
with Gnat2Why.Types;                     use Gnat2Why.Types;
with Gnat2Why.Util;                      use Gnat2Why.Util;
with Namet;                              use Namet;
with Nlists;                             use Nlists;
with Sem_Aux;                            use Sem_Aux;
with Sem_Ch12;                           use Sem_Ch12;
with Sem_Util;                           use Sem_Util;
with Sinfo;                              use Sinfo;
with Sinput;                             use Sinput;
with SPARK_Util;                         use SPARK_Util;
with SPARK_Util.External_Axioms;         use SPARK_Util.External_Axioms;
with SPARK_Util.Subprograms;             use SPARK_Util.Subprograms;
with SPARK_Util.Types;                   use SPARK_Util.Types;
with Stand;                              use Stand;
with String_Utils;                       use String_Utils;
with Why.Atree.Accessors;                use Why.Atree.Accessors;
with Why.Atree.Builders;                 use Why.Atree.Builders;
with Why.Atree.Modules;                  use Why.Atree.Modules;
with Why.Conversions;                    use Why.Conversions;
with Why.Gen.Arrays;                     use Why.Gen.Arrays;
with Why.Gen.Binders;                    use Why.Gen.Binders;
with Why.Gen.Decl;                       use Why.Gen.Decl;
with Why.Gen.Expr;                       use Why.Gen.Expr;
with Why.Gen.Names;                      use Why.Gen.Names;
with Why.Ids;                            use Why.Ids;
with Why.Inter;                          use Why.Inter;
with Why.Sinfo;                          use Why.Sinfo;
with Why.Types;                          use Why.Types;

package body Gnat2Why.External_Axioms is

   package List_Of_Entity is new
     Ada.Containers.Doubly_Linked_Lists (Entity_Id);

   procedure Add_Dependencies
     (E         : Entity_Id;
      G_Parents : List_Of_Entity.List);
   --  Add extra dependencies between entities declared in the generic
   --  and entities of the actual parameters.

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
   --  Returns the association list of a package instance entity

   function Get_Generic_Name (E : Entity_Id;
                              Parents : List_Of_Entity.Cursor)
                              return String;
   --  Returns the sequence of every scope of E where instances are replaced
   --  by generics.
   --  E should be an element of the path between Package_Entity and the
   --  first package with external axioms above it

   function Get_Generic_Parents (E : Entity_Id) return List_Of_Entity.List;
   --  Returns the list of every instance of generic package up to the first
   --  package with external axioms.

   function Get_Instance_Name (E : Entity_Id) return String is
     (Full_Name (E));
   --  Returns the name of a package instance entity

   function Get_Label_List (E : Entity_Id) return List_Id;
   --  Use Parent field to reach N_Generic_Package_Declaration
   --  ??? See Spark_Util.Iterate_Generic_Parameters

   procedure Parse_Parameters
     (Package_Entity : Entity_Id;
      G_Parents      : List_Of_Entity.List);
   --  Declares a Why type per formal of type kind of the first element of
   --  G_Parents and a Why function per formal of function kind of the first
   --  element of G_Parents

   procedure Register_External_Entities (E : Entity_Id);
   --  This function is called on a package with external axioms.
   --  It registers all entities in the global symbol table.

   ----------------------
   -- Add_Dependencies --
   ----------------------

   procedure Add_Dependencies
     (E         : Entity_Id;
      G_Parents : List_Of_Entity.List)
   is
      procedure Compute_Completions
        (Compl : out List_Of_Entity.List);
      --  Returns the list of the actuals of the generic parameters of
      --  G_Parents.

      procedure Add_Dependencies_Decls
        (Decls  : List_Id;
         C_List : List_Of_Entity.List);
      --  Add dependencies for actuals of the generic parameters to every
      --  declaration

      -------------------------
      -- Compute_Completions --
      -------------------------

      procedure Compute_Completions
        (Compl : out List_Of_Entity.List)
      is
         procedure Completion (Formal : Node_Id; Par : Node_Id);

         procedure Compute_Completions_Package is new
           Iterate_Generic_Parameters (Completion);

         ----------------
         -- Completion --
         ----------------

         procedure Completion (Formal : Node_Id; Par : Node_Id) is
            pragma Unreferenced (Formal);
            Actual : constant Entity_Id :=
              (if Nkind (Par) in N_Has_Entity
               and then Present (Entity (Par))
               then
                 (if Ekind (Entity (Par)) = E_Function then
                       Get_Renamed_Entity (Entity (Par))
                  else Entity (Par))
               else Empty);

         begin
            if Nkind (Actual) in N_Entity
              and then Ekind (Actual) in E_Function
            then
               List_Of_Entity.Append (Compl, Actual);
            end if;
         end Completion;

      --  Start of processing for Compute_Completions

      begin
         for GParent of G_Parents loop
            Compute_Completions_Package (GParent);
         end loop;
      end Compute_Completions;

      ----------------------------
      -- Add_Dependencies_Decls --
      ----------------------------

      procedure Add_Dependencies_Decls
        (Decls  : List_Id;
         C_List : List_Of_Entity.List)
      is
         N : Node_Id := First (Decls);
      begin
         while Present (N) loop
            if Comes_From_Source (N) then
               case Nkind (N) is
                  when N_Subtype_Declaration
                     | N_Private_Type_Declaration
                     | N_Subprogram_Declaration
                     | N_Object_Declaration
                  =>
                     declare
                        E : constant Entity_Id := Defining_Entity (N);
                     begin
                        --  Add the completion of actual parameters

                        for Completion of C_List loop
                           Add_Extra_Dependency (E, Completion);
                        end loop;
                     end;

                     --  Call Add_Dependencies_Decls recursively on
                     --  N_Package_Declaration and N_Package_Instantiation.

                  when N_Package_Instantiation =>
                     Add_Dependencies_Decls
                       (Decls  => Visible_Declarations
                          (Specification (Instance_Spec (N))),
                        C_List => C_List);

                  when N_Package_Declaration =>
                     Add_Dependencies_Decls
                       (Decls  =>
                           Visible_Declarations (Package_Specification (N)),
                        C_List => C_List);

                  when others =>
                     null;
               end case;
            end if;

            Next (N);
         end loop;
      end Add_Dependencies_Decls;

      C_List : List_Of_Entity.List;

      --  Start of processing for Add_Dependencies

   begin
      Compute_Completions (C_List);

      Add_Dependencies_Decls
        (Decls  => Visible_Declarations (Package_Specification (E)),
         C_List => C_List);
   end Add_Dependencies;

   --------------------------------
   -- Complete_External_Entities --
   --------------------------------

   procedure Complete_External_Entities (E : Entity_Id) is

      procedure Complete_Decls (Decls : List_Id);
      --  Complete declarations of type entities from the declaration list

      --------------------
      -- Complete_Decls --
      --------------------

      procedure Complete_Decls (Decls : List_Id) is
         N : Node_Id := First (Decls);
      begin
         while Present (N) loop

            --  For type declarations, generate a completion module

            if Comes_From_Source (N)
              and then Nkind (N) in
              N_Full_Type_Declaration
                | N_Private_Extension_Declaration
                  | N_Private_Type_Declaration
                    | N_Subtype_Declaration
            then
               declare
                  E  : constant Entity_Id := Defining_Entity (N);
               begin
                  if not Is_Standard_Boolean_Type (E)
                    and then E /= Universal_Fixed
                  then
                     declare
                        Compl_File : constant W_Section_Id :=
                          Dispatch_Entity_Completion (E);
                     begin
                        Generate_Type_Completion (Compl_File, E);
                     end;
                  end if;
               end;
            end if;

            --  Call Complete_Decls recursively on Package_Declaration and
            --  Package_Instantiation.

            if Comes_From_Source (N) and then
              Nkind (N) = N_Package_Instantiation
            then
               Complete_Decls
                 (Decls  => Visible_Declarations
                    (Specification (Instance_Spec (N))));
            end if;

            if Comes_From_Source (N) and then
              Nkind (N) in N_Package_Declaration
            then
               Complete_Decls
                 (Decls  => Visible_Declarations (Package_Specification (N)));
            end if;

            Next (N);
         end loop;
      end Complete_Decls;

   --  Start of processing for Complete_External_Entities

   begin

      --  If E is generic, complete type parameter declarations

      if Present (Generic_Parent (Package_Specification (E))) then
         declare
            Instance_Name : constant String := Get_Instance_Name (E);

            procedure Handle_Parameter (Form : Node_Id; Par : Node_Id);

            procedure Complete_Type_Param_Decl is new
              Iterate_Generic_Parameters (Handle_Parameter);

            ----------------------
            -- Handle_Parameter --
            ----------------------

            procedure Handle_Parameter (Form : Node_Id; Par : Node_Id)
            is
               Actual : constant Entity_Id :=
                 (if Nkind (Par) in N_Has_Entity
                  and then Present (Entity (Par))
                  then
                    (if Ekind (Entity (Par)) = E_Function then
                          Get_Renamed_Entity (Entity (Par))
                     else Entity (Par))
                  else Empty);

               Formal : constant Entity_Id := Defining_Entity (Form);
            begin
               if Is_Type (Formal)
                 and then not Is_Boolean_Type (Retysp (Actual))
                 and then not Is_Itype (Retysp (Actual))
               then
                  declare
                     Compl_File : constant W_Section_Id :=
                       Dispatch_Entity_Completion (Retysp (Actual));
                  begin

                     Open_Theory
                       (Compl_File,
                        Module =>
                          New_Module
                            (Name =>
                                 NID (Capitalize_First (Instance_Name)
                               & "__" & Short_Name (Formal)
                               & To_String (WNE_Axiom_Suffix)),
                             File => No_Name),
                        Comment =>
                          "Module giving axioms for the type entity "
                        & """" & Get_Name_String (Chars (E)) & """"
                        & (if Sloc (E) > 0 then
                             " defined at "
                          & Build_Location_String (Sloc (E)) else "")
                        & ", created in "
                        & GNAT.Source_Info.Enclosing_Entity);

                     Add_With_Clause
                       (Compl_File, E_Axiom_Module (Retysp (Actual)),
                        EW_Export);

                     Close_Theory (Compl_File,
                                   Defined_Entity => Formal,
                                   Kind => Axiom_Theory);
                  end;
               end if;
            end Handle_Parameter;

         begin
            Complete_Type_Param_Decl (E);
         end;
      end if;

      --  Complete other type declarations

      Complete_Decls
        (Decls  => Visible_Declarations (Package_Specification (E)));
   end Complete_External_Entities;

   --------------------
   -- Compute_Length --
   --------------------

   procedure Compute_Length (G_Parents    :     List_Of_Entity.List;
                             Subst_Length : out Natural) is

      procedure Compute_Length_Package (Labs         :        List_Id;
                                        Subst_Length : in out Natural);

      ----------------------------
      -- Compute_Length_Package --
      ----------------------------

      procedure Compute_Length_Package (Labs         :        List_Id;
                                        Subst_Length : in out Natural) is
         CurLabs  : Node_Id := First (Labs);
      begin
         Subst_Length := Subst_Length + 3;
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

      CurGParent : List_Of_Entity.Cursor := List_Of_Entity.First (G_Parents);

   --  Start of processing for Compute_Length

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
      Subst         : out W_Custom_Substitution_Array)
   is
      procedure Compute_Substitution_Package
        (Generic_Name  : String;
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
      Subst_Cur : Positive := 1;

      ----------------------------------
      -- Compute_Substitution_Package --
      ----------------------------------

      procedure Compute_Substitution_Package
        (Generic_Name  : String;
         Instance_Name : String)
      is
      begin
         --  Rename every module in the copy.
         --  Replace: <Generic_Name>__ by: <Instance_Name>__

         Subst (Subst_Cur) := New_Custom_Substitution
           (Domain   => EW_Prog,
            From     => NID (Capitalize_First (Generic_Name) & "__"),
            To       => W_Any_Node_Id
              (New_Identifier (Name =>
                                   Capitalize_First (Instance_Name) & "__")));

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

         --  Rename record_component in the copy.
         --  Replace: rec__<Generic_Name> by: rec__<Instance_Name>

         Subst (Subst_Cur) := New_Custom_Substitution
           (Domain   => EW_Prog,
            From     => NID ("rec__" & Generic_Name),
            To       => W_Any_Node_Id
              (New_Identifier (Name => "rec__" & Instance_Name)));

         Subst_Cur := Subst_Cur + 1;
      end Compute_Substitution_Package;

      GParent_Cur : List_Of_Entity.Cursor :=
        List_Of_Entity.First (G_Parents);

   begin
      while List_Of_Entity.Has_Element (GParent_Cur) loop
         declare
            E : constant Entity_Id := List_Of_Entity.Element (GParent_Cur);

            Generic_Name  : constant String :=
              Get_Generic_Name (E, GParent_Cur);

            Instance_Name : constant String := Get_Instance_Name (E);

            procedure Substitution (Form : Node_Id; Actual : Node_Id);

            procedure Compute_Substitution_P is new
              Iterate_Generic_Parameters (Substitution);

            ------------------
            -- Substitution --
            ------------------

            procedure Substitution (Form : Node_Id; Actual : Node_Id) is
               Actual_E : Entity_Id;
               Formal : constant Entity_Id := Defining_Entity (Form);
            begin
               if Is_Type (Formal) then

                  --  Make sure that it is safe to call Entity

                  pragma Assert (Nkind (Actual) in N_Has_Entity);

                  Actual_E := Entity (Actual);

                  --  Classwide types are represented by their underlying
                  --  tagged type. This matters here as we're using the name of
                  --  the actual type in the include declaration.

                  if Is_Class_Wide_Type (Actual_E) then
                     Actual_E := Specific_Tagged (Actual_E);
                  end if;

                  --  Replace:
                  --  use "<Generic_Name>__args".<Generic_Name>__<Formal>
                  --  by: use ("<Actual_File>".)Name_Of_Node (Actual_E)
                  --  No use is generated if Actual_E doesn't have a unique
                  --  name

                  if Full_Name_Is_Not_Unique_Name (Actual_E) then
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
                          (Name => "use " &
                             Capitalize_First (Full_Name (Actual_E))
                           & ASCII.LF)));
                  end if;
                  Subst_Cur := Subst_Cur + 1;

                  --  Replace: <Generic_Name>__<Formal>.<Formal>
                  --  by: Why_Logic_Type_Of_Ada_Type (Actual_E)

                  Subst (Subst_Cur) := New_Custom_Substitution
                    (Domain   => EW_Prog,
                     From     => NID (Capitalize_First (Generic_Name)
                       & "__" & Short_Name (Formal) & "\." &
                         Short_Name (Formal)),
                     To       => W_Any_Node_Id
                       (EW_Abstract (Actual_E)));

                  --  If the formal has a private kind, Base_Type_Name,
                  --  To_Base_Name, Of_Base_Name, and In_Range_Name must be
                  --  replaced appropriately

                  if Is_Private_Type (Formal) then
                     declare
                        Actual_Type : constant W_Type_OId :=
                          EW_Abstract (Actual_E);
                        Actual_Base : constant W_Type_OId :=
                          +Base_Why_Type (Unique_Entity (Actual_E));

                     begin

                        --  If the actual is a scalar type and not a bool:
                        --  <Generic_Name>__<Base_Type_Name> =>
                        --               Base_Why_Type (<Actual_E>)
                        --  <Generic_Name>__<To_Base_Name>   =>
                        --               Conversion_Name (To   => <Base>,
                        --                                From => <Actual_E>)
                        --  <Generic_Name>__<Of_Base_Name>   =>
                        --               Conversion_Name (From => <Base>,
                        --                                To   => <Actual_E>)
                        --  <Generic_Name>__<In_Range_Name>  =>
                        --               Range_Pred_Name (<Actual_E>)
                        --  Otherwise:
                        --  <Generic_Name>__<Base_Type_Name> => <Actual_E>
                        --  <Generic_Name>__<To_Base_Name>   =>
                        --  <Generic_Name>__<Of_Base_Name>   =>
                        --  <Generic_Name>__<In_Range_Name>  => __ignore

                        if Is_Scalar_Type (Actual_E) and then
                          not Is_Boolean_Type (Actual_E)
                        then
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
                                (Range_Pred_Name
                                     (if Type_Is_Modeled_As_Base (Actual_E)
                                      then Base_Type (Actual_E)
                                      else Actual_E)));
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
                     --  by: Name_Of_Node (Actual_E).

                     Subst (Subst_Cur + 1) := New_Custom_Substitution
                       (Domain   => EW_Prog,
                        From     => NID (Capitalize_First (Generic_Name)
                          & "__" & Short_Name (Formal) & "\."),
                        To       => W_Any_Node_Id
                          (New_Identifier (Name => Capitalize_First
                                           (Full_Name (Actual_E)) & ".")));
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
                        & "__" & Get_Name_String (Chars (Formal)) &
                          ASCII.LF)));
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
                             Module =>
                               New_Module
                                 (File => No_Name,
                                  Name =>
                                    NID (Capitalize_First (Instance_Name) &
                                        "__" &
                                        Get_Name_String (Chars (Formal)))))));
                  Subst_Cur := Subst_Cur + 1;

               elsif Ekind (Formal) = E_Generic_In_Parameter then

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
                     To       => W_Any_Node_Id (New_Identifier
                       (Name => Capitalize_First (Instance_Name)
                        & "__" & Short_Name (Formal) & "." &
                          Short_Name (Formal))));
                  Subst_Cur := Subst_Cur + 1;
               end if;
            end Substitution;

         begin
            Compute_Substitution_P (E);

            Compute_Substitution_Package
              (Generic_Name  => Generic_Name,
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
      --  Taverse the scope of E to compute its name

      function Get_Generic_Name_Scope
        (E : Entity_Id; N : List_Of_Entity.Cursor) return String is
      begin
         if List_Of_Entity.Has_Element (N) then

            --  If E is the next instance N, then use the name of its
            --  Generic_Parent instead.

            if List_Of_Entity.Element (N) = E then
               return
                 Get_Generic_Name_Scope
                   (Generic_Parent (Package_Specification (E)),
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

            --  If E has external axioms, return the empty list or E if it is
            --  generic itself.

            if Ekind (E) = E_Package and then
              Package_Has_Ext_Axioms (E)
            then
               Result := List_Of_Entity.Empty_List;
               Found := True;
               if Present (Generic_Parent (Package_Specification (E))) then
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
                 (Generic_Parent (Package_Specification (E)), Result, Found);
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

   --------------------
   -- Get_Label_List --
   --------------------

   function Get_Label_List (E : Entity_Id) return List_Id is
      P : Node_Id := Generic_Parent (Package_Specification (E));
   begin
      while Nkind (P) /= N_Generic_Package_Declaration loop
         P := Parent (P);
      end loop;

      return Generic_Formal_Declarations (P);
   end Get_Label_List;

   ----------------------
   -- Parse_Parameters --
   ----------------------

   procedure Parse_Parameters
     (Package_Entity : Entity_Id;
      G_Parents      : List_Of_Entity.List)
   is
      Assoc : constant List_Id := Get_Association_List (Package_Entity);
      Labs  : constant List_Id := Get_Label_List (Package_Entity);
      Instance_Name : constant String := Get_Instance_Name (Package_Entity);

      TFile : constant W_Section_Id := Dispatch_Entity (Package_Entity);

      procedure Handle_Actual_And_Formal (Form : Node_Id;
                                          Par  : Node_Id);

      procedure Parse_Param is new
        Iterate_Generic_Parameters (Handle_Actual_And_Formal);

      function Get_Logic_Type_Of_Ada_Type
        (Ty       : Node_Id;
         Is_Input : Boolean) return W_Type_Id;
      --  Take an Ada Node and transform it into a Why logic type. The Ada
      --  Node is expected to be a Defining_Identifier for a type.
      --  If Is_Input is True then returns the base_type if base_type should
      --  be used.

      function Get_Actual_Type_Of_Ada_Generic_Type
        (Ty       : Node_Id) return Entity_Id;
      --  Return the associated actual if Ty is a generic formal parameter.

      ------------------------------
      -- Handle_Actual_And_Formal --
      ------------------------------

      procedure Handle_Actual_And_Formal (Form : Node_Id;
                                          Par  : Node_Id)
      is
         Actual : constant Entity_Id :=
              (if Nkind (Par) in N_Has_Entity
                 and then Present (Entity (Par))
               then
                 (if Ekind (Entity (Par)) = E_Function then
                    Get_Renamed_Entity (Entity (Par))
                  else Entity (Par))
               else Empty);

         Formal : constant Entity_Id := Defining_Entity (Form);
      begin
         if Ekind (Formal) = E_Generic_In_Parameter then
            declare
               Typ    : constant W_Type_Id := Type_Of_Node (Etype (Formal));
               Def    : W_Term_Id;
               Params : constant Transformation_Params :=
                 (File        => TFile,
                  Phase       => Generate_Logic,
                  Gen_Marker  => False,
                  Ref_Allowed => False);

            begin
               --  Start with opening the theory to define, as the creation
               --  of a function for the logic term needs the current theory
               --  to insert an include declaration.

               Open_Theory
                 (TFile,
                  Module =>
                    New_Module
                      (Name =>
                           NID (Capitalize_First (Instance_Name) & "__"
                         & Short_Name (Formal)),
                       File => No_Name),
                  Comment =>
                    "Module for defining a constant for the formal "
                  & """" & Get_Name_String (Chars (Formal)) & """"
                  & (if Sloc (Formal) > 0 then
                       " defined at " & Build_Location_String (Sloc (Formal))
                    else "")
                  & ", created in " & GNAT.Source_Info.Enclosing_Entity);

               --  We generate a "logic", whose axiom will be given

               Emit (TFile,
                     Why.Atree.Builders.New_Function_Decl
                       (Domain      => EW_Term,
                        Name        =>
                          To_Why_Id (Formal, Domain => EW_Term, Local => True),
                        Binders     => (1 .. 0 => <>),
                        Labels      => Name_Id_Sets.Empty_Set,
                        Return_Type => Typ));

               Def :=
                 (if Present (Actual) then
                       +Transform_Identifier
                    (Params, Actual, Actual, Domain => EW_Term)
                  else
                     +Transform_Expr (Par, EW_Term, Params));

               if Def /= Why_Empty then
                  Emit
                    (TFile,
                     New_Defining_Axiom
                       (Ada_Node    => Formal,
                        Name        =>
                          To_Why_Id (Formal, Domain => EW_Term, Local => True),
                        Binders     => (1 .. 0 => <>),
                        Def         => Def));
               end if;

               Close_Theory (TFile,
                             Kind => Definition_Theory,
                             Defined_Entity => Formal);
            end;

            --  ??? The use of Full_Name_Is_Not_Unique_Name below does not
            --  correspond to the description of this subprogram. Comment on
            --  declaration of Full_Name_Is_Not_Unique_Name should be updated.

         elsif Is_Type (Formal) and then
           not Full_Name_Is_Not_Unique_Name (Formal)
         then
            --  For type parameters, generate a theory that renames the
            --  theory of the actual. Necessary for conversion functions.

            Open_Theory
              (TFile,
               Module =>
                 New_Module
                   (Name =>
                        NID (Capitalize_First (Instance_Name) & "__"
                      & Short_Name (Formal)),
                    File => No_Name),
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
                 (TFile,
                  New_Type_Decl
                    (Name  =>
                         New_Name (Symbol => NID (Short_Name (Formal))),
                     Alias => Type_Of_Node (Actual)));
            end if;

            Close_Theory (TFile,
                          Kind => Definition_Theory);

         elsif Ekind (Formal) = E_Function
           and then Ekind (Actual) = E_Function
         then

            --  Check that the function actual is pure

            if Flow_Utility.Has_Proof_Global_Reads (Actual,
                                                    Classwide => True)
            then
               Error_Msg_FE
                 ("non-pure actual & in instance with external axioms not"
                  & " yet supported", Package_Entity, Actual);
            end if;

            Open_Theory
              (TFile,
               New_Module
                 (File => No_Name,
                  Name =>
                    NID (Capitalize_First (Instance_Name) & "__"
                      & Get_Name_String (Chars (Formal)))),
               Comment =>
                 "Module for declaring a logic function for the formal "
               & """" & Get_Name_String (Chars (Formal)) & """"
               & (if Sloc (Formal) > 0 then
                    " defined at " &
                    Build_Location_String (Sloc (Formal))
                 else "")
               & ", created in " & GNAT.Source_Info.Enclosing_Entity);

            if Is_Generic_Actual_Subprogram (Actual) then
               pragma Assert (Is_Expression_Function (Actual));

               --  Happens for default subprogram actuals.
               --  Use the definition in Actual:
               --  function <formal> "inline" (x1 : ty_formal_1, ...)
               --                        : ty_formal = <def_actual>

               declare
                  Expr_Fun_N         : constant Node_Id :=
                    Get_Expression_Function (Actual);
                  Raw_Binders        : constant Item_Array :=
                    Compute_Subprogram_Parameters  (Actual, EW_Term);
                  Why_Type           : constant W_Type_Id :=
                    Type_Of_Node (Etype (Actual));
                  Logic_Why_Binders  : constant Binder_Array :=
                    To_Binder_Array ((if Raw_Binders'Length = 0 then
                                         (1 => (Regular, Unit_Param))
                                     else Raw_Binders));
                  Logic_Id           : constant W_Identifier_Id :=
                    To_Why_Id (Actual, Domain => EW_Term, Local => True);
                  Params             : constant Transformation_Params :=
                    (File        => TFile,
                     Phase       => Generate_Logic,
                     Gen_Marker   => False,
                     Ref_Allowed => False);
               begin
                  Ada_Ent_To_Why.Push_Scope (Symbol_Table);

                  --  Function parameters should not be split nor have
                  --  effects.

                  for Binder of Raw_Binders loop
                     declare
                        A : constant Node_Id :=
                          (case Binder.Kind is
                              when Regular => Binder.Main.Ada_Node,
                              when others  => raise Program_Error);
                     begin

                        pragma Assert (Present (A));

                        if Present (A) then
                           Ada_Ent_To_Why.Insert (Symbol_Table,
                                                  Unique_Entity (A),
                                                  Binder);
                        end if;
                     end;
                  end loop;

                  Emit
                    (TFile,
                     New_Function_Decl
                       (Domain      => EW_Term,
                        Name        => Logic_Id,
                        Binders     => Logic_Why_Binders,
                        Labels      =>
                          Name_Id_Sets.To_Set (NID ("inline")),
                        Return_Type => Why_Type,
                        Def         =>
                          +Transform_Expr
                          (Expression (Expr_Fun_N),
                           Expected_Type => Why_Type,
                           Domain        => EW_Term,
                           Params        => Params)));

                  Ada_Ent_To_Why.Pop_Scope (Symbol_Table);
               end;
            else

               --  For function parameters, generate a new function
               --  that introduced the needed conversions:
               --  function <formal> "inline" (x1 : ty_formal_1, ...)
               --                        : ty_formal =
               --  <ty_actual__to__ty_formal> (<actual>
               --      (<ty_formal1__to__ty_actual1> (x1)) ...)

               Add_Use_For_Entity
                 (P               => TFile,
                  N               => Actual,
                  Use_Kind        => EW_Clone_Default,
                  With_Completion => False);

               declare
                  F_Params : constant List_Id :=
                    Parameter_Specifications
                      (Subprogram_Specification (Formal));
                  F_Param : Node_Id := First (F_Params);
                  F_Type : constant W_Type_Id :=
                    Get_Logic_Type_Of_Ada_Type
                      (Get_Actual_Type_Of_Ada_Generic_Type (Etype (Formal)),
                       False);
                  A_Params : constant List_Id :=
                    Parameter_Specifications
                      (Subprogram_Specification (Actual));
                  A_Param : Node_Id := First (A_Params);
                  A_Type : constant W_Type_Id :=
                    Type_Of_Node (Etype (Actual));
                  Binders : Binder_Array
                    (1 .. Natural (List_Length (F_Params)));
                  Args    : W_Expr_Array
                    (1 .. Natural (List_Length (F_Params)));
                  Count : Positive := 1;
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
                           else Type_Of_Node (Etype (A_Id)));
                        F_Id   : constant Node_Id :=
                          Defining_Identifier (F_Param);
                        F_Type : constant W_Type_Id :=
                          Get_Logic_Type_Of_Ada_Type
                            (Get_Actual_Type_Of_Ada_Generic_Type
                               (Etype (F_Id)), True);
                        Name : constant W_Identifier_Id :=
                          New_Identifier
                            (Ada_Node => Empty,
                             Name => Full_Name (F_Id),
                             Typ  => F_Type);
                     begin
                        Binders (Count) :=
                          (Ada_Node => F_Id,
                           B_Name   => Name,
                           B_Ent    => Null_Entity_Name,
                           Mutable  => False);

                        Args (Count) := Insert_Simple_Conversion
                          (Domain        => EW_Term,
                           Expr          => +Name,
                           To            => +A_Type);

                        Next (F_Param);
                        Next (A_Param);
                        Count := Count + 1;
                     end;
                  end loop;

                  Emit
                    (TFile,
                     New_Function_Decl
                       (Domain      => EW_Term,
                        Name        =>
                          New_Identifier (Name => Short_Name (Formal)),
                        Binders     => Binders,
                        Return_Type => F_Type,
                        Labels      =>
                          Name_Id_Sets.To_Set (NID ("inline")),
                        Def         =>
                          Insert_Simple_Conversion
                            (Domain        => EW_Term,
                             Expr          => New_Call
                               (Domain   => EW_Term,
                                Name     => To_Why_Id (Actual,
                                  Domain => EW_Term),
                                Args     => Args,
                                Typ      => A_Type),
                             To            => F_Type)));

               end;
            end if;

            Close_Theory (TFile,
                          Kind => Definition_Theory);
         elsif Ekind (Formal) = E_Function
           and then Ekind (Actual) = E_Operator
         then

            --  For function parameters, generate a new function
            --  that introduced the needed conversions:
            --  function <formal> "inline" (x1 : ty_formal_1,
            --                              x2 : ty_formal_2)
            --                        : ty_formal =
            --  <ty_actual__to__ty_formal> (
            --      (<ty_formal1__to__ty_actual1> (x1)) <actual>
            --      (<ty_formal2__to__ty_actual2> (x2)))

            Open_Theory
              (TFile,
               New_Module
                 (Name => NID (Capitalize_First (Instance_Name) & "__"
                  & Get_Name_String (Chars (Formal))),
                  File => No_Name),
               Comment =>
                 "Module for declaring a logic function for the formal "
               & """" & Get_Name_String (Chars (Formal)) & """"
               & (if Sloc (Formal) > 0 then
                    " defined at " &
                    Build_Location_String (Sloc (Formal))
                 else "")
               & ", created in " & GNAT.Source_Info.Enclosing_Entity);

            declare
               F_Params : constant List_Id :=
                 Parameter_Specifications
                   (Subprogram_Specification (Formal));
               F_Param  : Node_Id := First (F_Params);
               F_Type   : constant Entity_Id :=
                 Get_Actual_Type_Of_Ada_Generic_Type (Etype (Formal));
               F_W_Type : constant W_Type_Id :=
                 Get_Logic_Type_Of_Ada_Type (F_Type, False);
               Binders  : Binder_Array
                 (1 .. Natural (List_Length (F_Params)));
               Left     : W_Expr_Id := Why_Empty;
               Right    : W_Expr_Id;
               Left_Ty  : Entity_Id := Empty;
               Right_Ty : Entity_Id;
               Count    : Positive := 1;
               Op       : constant N_Op :=
                 (if List_Length (F_Params) = 1 then
                       Get_Unary_Nkind (Actual)
                  else Get_Binary_Nkind (Actual));
            begin

               while Present (F_Param) loop
                  declare
                     F_Id   : constant Node_Id :=
                       Defining_Identifier (F_Param);
                     F_Type   : constant Entity_Id :=
                       Get_Actual_Type_Of_Ada_Generic_Type (Etype (F_Id));
                     F_W_Type : constant W_Type_Id :=
                       Get_Logic_Type_Of_Ada_Type (F_Type, True);
                     Name : constant W_Identifier_Id :=
                       New_Identifier
                         (Ada_Node => Empty,
                          Name => Full_Name (F_Id),
                          Typ  => F_W_Type);
                     M : constant W_Module_Id :=
                       (case Get_Type_Kind (F_W_Type) is
                           when EW_Builtin =>
                          (if F_W_Type = EW_Bool_Type then M_Boolean.Module
                           elsif F_W_Type = EW_Fixed_Type then
                              M_Integer.Module
                           elsif F_W_Type = EW_Int_Type then
                              M_Integer.Module
                           elsif F_W_Type = EW_Float_32_Type then
                              M_Floats (Float32).Module
                           elsif F_W_Type = EW_Float_64_Type then
                              M_Floats (Float64).Module
                           elsif F_W_Type = EW_BitVector_8_Type then
                              M_BVs (BV8).Module
                           elsif F_W_Type = EW_BitVector_16_Type then
                              M_BVs (BV16).Module
                           elsif F_W_Type = EW_BitVector_32_Type then
                              M_BVs (BV32).Module
                           elsif F_W_Type = EW_BitVector_64_Type then
                              M_BVs (BV64).Module
                           else M_Main.Module),
                           when EW_Abstract | EW_Split =>
                              E_Module (Get_Ada_Node (+F_W_Type)));
                  begin
                     Add_With_Clause (TFile,
                                      M,
                                      EW_Clone_Default);
                     Binders (Count) :=
                       (Ada_Node => F_Id,
                        B_Name   => Name,
                        B_Ent    => Null_Entity_Name,
                        Mutable  => False);

                     if Count = Natural (List_Length (F_Params)) then
                        Right := +Name;
                        Right_Ty := F_Type;
                     else
                        Left := +Name;
                        Left_Ty := F_Type;
                     end if;

                     Next (F_Param);
                     Count := Count + 1;
                  end;
               end loop;

               Emit
                 (TFile,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        =>
                       New_Identifier (Name => Short_Name (Formal)),
                     Binders     => Binders,
                     Return_Type => F_W_Type,
                     Labels      =>
                       Name_Id_Sets.To_Set (NID ("inline")),
                     Def         =>
                       Insert_Simple_Conversion
                         (Domain   => EW_Term,
                          Expr     =>
                            New_Op_Expr
                              (Op          => Op,
                               Left        => Left,
                               Right       => Right,
                               Left_Type   => Left_Ty,
                               Right_Type  => Right_Ty,
                               Return_Type => F_Type,
                               Domain      => EW_Term),
                          To       => F_W_Type)));

               Close_Theory (TFile,
                             Kind => Definition_Theory);
            end;
         end if;
      end Handle_Actual_And_Formal;

      -----------------------------------------
      -- Get_Actual_Type_Of_Ada_Generic_Type --
      -----------------------------------------

      function Get_Actual_Type_Of_Ada_Generic_Type
        (Ty         : Node_Id) return Entity_Id is

         --  Goes through a list of parameters to find actual that is
         --  associated with the formal Ty
         function Find_Actual
           (Assoc : List_Id;
            Labs  : List_Id) return Node_Id;

         function Find_Actual
           (Assoc : List_Id;
            Labs  : List_Id) return Node_Id is

            CurAssoc : Node_Id := First (Assoc);
            CurLabs  : Node_Id := First (Labs);
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

               while List_Of_Entity.Has_Element (CurGParent)
                 and then No (Actual)
               loop
                  Actual := Find_Actual
                    (Assoc => Get_Association_List (
                     List_Of_Entity.Element (CurGParent)),
                     Labs  => Get_Label_List (
                       List_Of_Entity.Element (CurGParent)));

                  List_Of_Entity.Next (CurGParent);
               end loop;

               pragma Assert (Present (Actual));

               return Actual;
            end;
         else
            return Ty;
         end if;
      end Get_Actual_Type_Of_Ada_Generic_Type;

      --------------------------------
      -- Get_Logic_Type_Of_Ada_Type --
      --------------------------------

      function Get_Logic_Type_Of_Ada_Type
        (Ty       : Node_Id;
         Is_Input : Boolean) return W_Type_Id is
      begin
         if Is_Input and then
           Use_Base_Type_For_Type (Ty)
         then

            --  If Is_Input is true, checks wether the base_type of
            --  Ty should be used.

            return Base_Why_Type (Unique_Entity (Ty));
         else
            return Type_Of_Node (Ty);
         end if;
      end Get_Logic_Type_Of_Ada_Type;

   --  Start of processing for Parse_Parameters

   begin
      Parse_Param (Package_Entity);
   end Parse_Parameters;

   --------------------------------
   -- Register_External_Entities --
   --------------------------------

   procedure Register_External_Entities (E : Entity_Id) is

      procedure Register_Decls (Decls : List_Id);
      --  Register the entities of the declarations

      function Get_Subp_Symbol
        (E    : Entity_Id;
         Name : String) return Binder_Type
      is
         (Binder_Type'(B_Name   => New_Identifier
                         (Ada_Node => E,
                          Name     => Name,
                          Module   => E_Module (E),
                          Typ      => Type_Of_Node (Etype (E))),
                       B_Ent    => Null_Entity_Name,
                       Ada_Node => E,
                       Mutable  => False));

      --------------------
      -- Register_Decls --
      --------------------

      procedure Register_Decls (Decls : List_Id) is
         N : Node_Id := First (Decls);
      begin
         while Present (N) loop

            --  A subprogram may have been rewritten by the frontend, in
            --  particular, it happens for expression functions. In this case,
            --  the declaration won't come from source but its original node
            --  will.

            if (Comes_From_Source (N)
                or else (Present (Original_Node (N))
                         and then Comes_From_Source (Original_Node (N))))
              and then Nkind (N) in N_Subprogram_Declaration
              | N_Object_Declaration
            then
               declare
                  E : constant Entity_Id := Defining_Entity (N);
                  Name : constant String := Short_Name (E);
                  Logic_Name : constant String :=
                    Name & "__logic";
               begin
                  if Ekind (E) = E_Function then
                     Ada_Ent_To_Why.Insert
                       (Symbol_Table, E,
                        Item_Type'(Func,
                          For_Logic => Get_Subp_Symbol (E, Logic_Name),
                          For_Prog  => Get_Subp_Symbol (E, Name)));
                  elsif Ekind (E) = E_Procedure then
                     Insert_Entity
                       (E,
                        To_Why_Id (E, Domain => EW_Term),
                        Mutable => False);
                  else
                     Ada_Ent_To_Why.Insert
                       (Symbol_Table, E, Mk_Item_Of_Entity (E));
                  end if;
               end;
            end if;

            --  If there is a user declaration of an array type, possibly
            --  create a new type of array by cloning underlying Why3 theories.
            --  If the type of the array's component is declared locally to the
            --  package with external axioms, it is the responsability of the
            --  theory file to provide the new array type.

            if Comes_From_Source (N)
              and then Nkind (N) = N_Full_Type_Declaration
              and then Is_Array_Type (Defining_Identifier (N))
            then
               declare
                  File : constant W_Section_Id :=
                    Dispatch_Entity (Defining_Identifier (N));
                  Element_Is_Local : constant Boolean :=
                    Containing_Package_With_Ext_Axioms
                      (Component_Type (Defining_Identifier (N))) = E;
               begin
                  Create_Rep_Array_Theory_If_Needed
                    (File          => File,
                     E             => Defining_Identifier (N),
                     Register_Only => Element_Is_Local);
               end;
            end if;

            --  Call Register_Decls recursively on Package_Declaration and
            --  Package_Instantiation.

            if Comes_From_Source (N) and then
              Nkind (N) = N_Package_Instantiation
            then
               Register_Decls
                 (Decls  => Visible_Declarations
                    (Specification (Instance_Spec (N))));
            end if;

            if Comes_From_Source (N) and then
              Nkind (N) in N_Package_Declaration
            then
               Register_Decls
                 (Decls  => Visible_Declarations (Package_Specification (N)));
            end if;

            Next (N);
         end loop;
      end Register_Decls;

   --  Start of processing for Register_External_Entities

   begin
      Register_Decls
        (Decls  => Visible_Declarations (Package_Specification (E)));
   end Register_External_Entities;

   --------------------------------------------
   -- Translate_Package_With_External_Axioms --
   --------------------------------------------

   procedure Translate_Package_With_External_Axioms
     (Package_Entity : Entity_Id)
   is

      TFile : Why_Section renames
        Why_Sections (Dispatch_Entity (Package_Entity));
      G_Parents : constant List_Of_Entity.List :=
        Get_Generic_Parents (Package_Entity);
      Subst_Length : Natural;

   --  Start of processing for Translate_Package_With_External_Axioms

   begin
      Register_External_Entities (Package_Entity);

      if List_Of_Entity.Is_Empty (G_Parents) then
         declare
            Decl : constant W_Custom_Declaration_Id :=
              New_Custom_Declaration
              (Ada_Node  => Package_Entity,
               Domain    => EW_Prog,
               File_Name => NID (Full_Name (Package_Entity) & ".mlw"));
         begin
            TFile.Theories.Append (Why_Node_Id (Decl));
         end;
      else
         --  Translation will always be called on top-level packages with
         --  external axiomatization only, that is, either packages with
         --  no generic parents or instances of generic packages.

         pragma Assert
           (List_Of_Entity.First_Element (G_Parents) = Package_Entity);

         Parse_Parameters (Package_Entity, G_Parents);

         Compute_Length (G_Parents, Subst_Length);

         declare
            Subst : W_Custom_Substitution_Array (1 .. Subst_Length);
         begin
            Compute_Substitution (G_Parents, Subst);
            declare
               Decl : constant W_Custom_Declaration_Id :=
                 New_Custom_Declaration
                   (Domain    => EW_Prog,
                    File_Name =>
                      NID (Get_Generic_Name (Package_Entity,
                        List_Of_Entity.First (G_Parents)) & ".mlw"),
                    Subst     => Subst);
            begin
               TFile.Theories.Append (Why_Node_Id (Decl));
               Add_Dependencies (Package_Entity, G_Parents);
            end;
         end;
      end if;
   end Translate_Package_With_External_Axioms;

end Gnat2Why.External_Axioms;
