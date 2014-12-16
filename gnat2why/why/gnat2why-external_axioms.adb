------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              G N A T 2 W H Y - E X T E R N A L _ A X I O M S             --
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

with GNAT.Source_Info;

with Atree;                use Atree;
with Einfo;                use Einfo;
with Errout;               use Errout;
with Namet;                use Namet;
with Nlists;               use Nlists;
with Sem_Aux;              use Sem_Aux;
with Sem_Ch12;             use Sem_Ch12;
with Sem_Util;             use Sem_Util;
with Sinfo;                use Sinfo;
with Sinput;               use Sinput;
with String_Utils;         use String_Utils;

with SPARK_Util;           use SPARK_Util;
with Flow_Utility;         use Flow_Utility;

with Why.Ids;              use Why.Ids;
with Why.Sinfo;            use Why.Sinfo;
with Why.Atree.Accessors;  use Why.Atree.Accessors;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Atree.Mutators;   use Why.Atree.Mutators;
with Why.Atree.Modules;    use Why.Atree.Modules;
with Why.Gen.Decl;         use Why.Gen.Decl;
with Why.Gen.Names;        use Why.Gen.Names;
with Why.Gen.Binders;      use Why.Gen.Binders;
with Why.Gen.Expr;         use Why.Gen.Expr;
with Why.Inter;            use Why.Inter;
with Why.Types;            use Why.Types;
with Why.Conversions;      use Why.Conversions;

with Gnat2Why.Expr;        use Gnat2Why.Expr;
with Gnat2Why.Nodes;       use Gnat2Why.Nodes;
with Gnat2Why.Util;        use Gnat2Why.Util;
with Gnat2Why.Decls;       use Gnat2Why.Decls;
with Gnat2Why.Subprograms; use Gnat2Why.Subprograms;

with Ada.Containers.Doubly_Linked_Lists;
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
   --  package with external axioms

   function Get_Instance_Name (E : Entity_Id) return String is
     (Capitalize_First (Full_Name (E)));
   --  Returns the name of a package instance entity

   function Get_Label_List (E : Entity_Id) return List_Id;
   --  Use Parent field to reach N_Generic_Package_Declaration

   procedure Parse_Parameters (Package_Entity : Entity_Id;
                               G_Parents : List_Of_Entity.List);
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
         procedure Compute_Completions_Package (Assoc : List_Id);

         ---------------------------------
         -- Compute_Completions_Package --
         ---------------------------------

         procedure Compute_Completions_Package (Assoc : List_Id) is
            CurAssoc : Node_Id := First (Assoc);
         begin
            while Present (CurAssoc) loop
               declare
                  Actual : constant Entity_Id :=
                    Entity (Explicit_Generic_Actual_Parameter (CurAssoc));
               begin
                  if Ekind (Actual) = E_Function then
                     List_Of_Entity.Append (Compl, Actual);
                  end if;
               end;
               Next (CurAssoc);
            end loop;
         end Compute_Completions_Package;

         --  Start of Compute_Completions

      begin
         for GParent of G_Parents loop
            Compute_Completions_Package
              (Generic_Associations
                 (Get_Package_Instantiation_Node (GParent)));
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
                     | N_Object_Declaration =>
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
                           Visible_Declarations (Get_Package_Spec (N)),
                        C_List => C_List);

                  when others =>
                     null;
               end case;
            end if;

            Next (N);
         end loop;
      end Add_Dependencies_Decls;

      C_List : List_Of_Entity.List;

      --  Start of Add_Dependencies

   begin
      Compute_Completions (C_List);

      Add_Dependencies_Decls
        (Decls  => Visible_Declarations (Get_Package_Spec (E)),
         C_List => C_List);
   end Add_Dependencies;

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
      Subst         : out W_Custom_Substitution_Array)
   is
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

      ----------------------------------
      -- Compute_Substitution_Package --
      ----------------------------------

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
               Actual : Entity_Id :=
                 Entity (Explicit_Generic_Actual_Parameter (CurAssoc));
               Formal : constant Entity_Id := Defining_Entity (CurLabs);

            begin
               --  Classwide types are represented by their underlying tagged
               --  type. This matters here as we're using the name of the
               --  actual type in the include declaration.

               if Ekind (Actual) in E_Class_Wide_Type | E_Class_Wide_Subtype
               then
                  Actual := Corresponding_Tagged (Actual);
               end if;

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
                          (Name => "use " &
                             Capitalize_First (Full_Name (Actual))
                           & ASCII.LF)));
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
                          not Is_Boolean_Type (Actual)
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
                                           (Full_Name (Actual)) & ".")));
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

               --  When do we reach here???

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
                        (Full_Name (Actual)) & ASCII.LF)));
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
              Package_Has_External_Axioms (E)
            then
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

   procedure Parse_Parameters (Package_Entity : Entity_Id;
                               G_Parents : List_Of_Entity.List) is
      Assoc : constant List_Id :=  Get_Association_List (Package_Entity);
      Labs  : constant List_Id :=  Get_Label_List (Package_Entity);
      Instance_Name : constant String := Get_Instance_Name (Package_Entity);

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

               return Actual;
            end;
         else
            return Ty;
         end if;
      end Get_Actual_Type_Of_Ada_Generic_Type;

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
            return EW_Abstract (Ty);
         end if;
      end Get_Logic_Type_Of_Ada_Type;

      TFile     : Why_Section :=
        Why_Sections (Dispatch_Entity (Package_Entity));
      CurAssoc  : Node_Id := First (Assoc);
      CurLabs   : Node_Id := First (Labs);

   begin
      while Present (CurAssoc) loop
         declare
            Par    : constant Node_Id :=
              Explicit_Generic_Actual_Parameter (CurAssoc);
            A      : constant Entity_Id := Entity (Par);
            Actual : constant Entity_Id :=
              (if Ekind (A) = E_Function then
                  Get_Renamed_Entity (A)
               else A);
            Formal : constant Entity_Id := Defining_Entity (CurLabs);

         begin
            --  For a constant parameter, generate a theory similar to
            --  those for other constants, except it contains here both the
            --  declaration of the constant function, and possibly the axiom
            --  for the definition.

            if Ekind (Formal) = E_Generic_In_Parameter then
               declare
                  Typ  : constant W_Type_Id  := EW_Abstract (Etype (Formal));
                  Def  : W_Term_Id;
                  Params             : constant Transformation_Params :=
                    (File        => TFile.File,
                     Theory      => TFile.Cur_Theory,
                     Phase       => Generate_Logic,
                     Gen_Marker   => False,
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

                  Emit (TFile.Cur_Theory,
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
                       (TFile.Cur_Theory,
                        New_Defining_Axiom
                          (Ada_Node    => Formal,
                           Name        =>
                         To_Why_Id (Formal, Domain => EW_Term, Local => True),
                           Return_Type => Get_Base_Type (Typ),
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

            elsif Ekind (Formal) in Type_Kind and then
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
                    (TFile.Cur_Theory,
                     New_Type_Decl
                       (Name  =>
                            New_Name (Symbol => NID (Short_Name (Formal))),
                        Alias => EW_Abstract (Actual)));
               end if;

               if Ekind (Actual) in E_Record_Type and then
                 Root_Record_Type (Actual) = Actual
               then

                  --  if the actual is a root type of a record type, we need
                  --  to define the conversion functions

                  declare
                     F_Ty   : constant W_Type_Id :=
                       +New_Named_Type (Short_Name (Formal));
                     A_Ident    : constant W_Identifier_Id :=
                       New_Identifier (Name => "a", Typ => F_Ty);
                     R_Binder   : constant Binder_Array :=
                       (1 => (B_Name => A_Ident,
                              others => <>));
                  begin

                     Emit
                       (TFile.Cur_Theory,
                        New_Function_Decl
                          (Domain      => EW_Term,
                           Name        => To_Ident (WNE_To_Base),
                           Binders     => R_Binder,
                           Labels      => Name_Id_Sets.Empty_Set,
                           Return_Type => F_Ty,
                           Def         => +A_Ident));
                     Emit
                       (TFile.Cur_Theory,
                        New_Function_Decl
                          (Domain      => EW_Term,
                           Name        => To_Ident (WNE_Of_Base),
                           Binders     => R_Binder,
                           Labels      => Name_Id_Sets.Empty_Set,
                           Return_Type => F_Ty,
                           Def         => +A_Ident));

                  end;
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
                       EW_Abstract (Etype (Actual));
                     Logic_Why_Binders  : constant Binder_Array :=
                       To_Binder_Array ((if Raw_Binders'Length = 0 then
                                            (1 => (Regular, Unit_Param))
                                        else Raw_Binders));
                     Logic_Id           : constant W_Identifier_Id :=
                       To_Why_Id (Actual, Domain => EW_Term, Local => True);
                     Params             : constant Transformation_Params :=
                       (File        => TFile.File,
                        Theory      => TFile.Cur_Theory,
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
                       (TFile.Cur_Theory,
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
                         (Get_Subprogram_Spec (Formal));
                     F_Param : Node_Id := First (F_Params);
                     F_Type : constant W_Type_Id :=
                       Get_Logic_Type_Of_Ada_Type
                         (Get_Actual_Type_Of_Ada_Generic_Type (Etype (Formal)),
                          False);
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
                              B_Ent    => null,
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
                       (TFile.Cur_Theory,
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
                      (Get_Subprogram_Spec (Formal));
                  F_Param  : Node_Id := First (F_Params);
                  F_Type   : constant Entity_Id :=
                    Get_Actual_Type_Of_Ada_Generic_Type (Etype (Formal));
                  F_W_Type : constant W_Type_Id :=
                    Get_Logic_Type_Of_Ada_Type (F_Type, False);
                  Binders  : Binder_Array
                    (1 .. Integer (List_Length (F_Params)));
                  Left     : W_Expr_Id := Why_Empty;
                  Right    : W_Expr_Id;
                  Left_Ty  : Entity_Id := Empty;
                  Right_Ty : Entity_Id;
                  Count    : Integer := 1;
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
                          (case Get_Base_Type (F_W_Type) is
                              when EW_Int | EW_Fixed => Integer_Module,
                              when EW_Real => Floating_Module,
                              when EW_Bool => Boolean_Module,
                              when EW_Unit .. EW_Prop => Main_Module,
                              when EW_Abstract | EW_Split | EW_Private =>
                                 E_Module (Get_Ada_Node (+F_W_Type)));
                     begin
                        Add_With_Clause (TFile.Cur_Theory,
                                         M,
                                         EW_Clone_Default);
                        Binders (Count) :=
                          (Ada_Node => F_Id,
                           B_Name   => Name,
                           B_Ent    => null,
                           Mutable  => False);

                        if Count = Integer (List_Length (F_Params)) then
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
                    (TFile.Cur_Theory,
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
         end;
         Next (CurAssoc);
         Next (CurLabs);
      end loop;
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
                          Typ      => EW_Abstract (Etype (E))),
                       B_Ent    => null,
                       Ada_Node => E,
                       Mutable  => False));

      --------------------
      -- Register_Decls --
      --------------------

      procedure Register_Decls (Decls : List_Id) is
         N : Node_Id := First (Decls);
      begin
         while Present (N) loop
            if Comes_From_Source (N) and then
              Nkind (N) in
              N_Subprogram_Declaration | N_Object_Declaration
            then
               declare
                  E : constant Entity_Id := Defining_Entity (N);
                  Name : constant String := Short_Name (E);
                  Logic_Name : constant String :=
                    Name & To_String (WNE_Logic_Fun_Suffix);
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
                     Insert_Entity
                       (E,
                        To_Why_Id (E, Typ => EW_Abstract (Etype (E)),
                                   Domain => EW_Term),
                        Mutable => Ekind (E) in Object_Kind and then
                        Is_Mutable_In_Why (E));
                  end if;
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
                 (Decls  => Visible_Declarations (Get_Package_Spec (N)));
            end if;

            Next (N);
         end loop;
      end Register_Decls;

   --  Start of Register_External_Entities

   begin
      Register_Decls
        (Decls  => Visible_Declarations (Get_Package_Spec (E)));
   end Register_External_Entities;

   --------------------------------------------
   -- Translate_Package_With_External_Axioms --
   --------------------------------------------

   procedure Translate_Package_With_External_Axioms
     (Package_Entity : Entity_Id)
   is

      TFile : constant Why_Section :=
        Why_Sections (Dispatch_Entity (Package_Entity));
      G_Parents : constant List_Of_Entity.List :=
        Get_Generic_Parents (Package_Entity);
      Subst_Length : Natural;

   --  Start of Translate_Package_With_External_Axioms

   begin
      Register_External_Entities (Package_Entity);

      if List_Of_Entity.Is_Empty (G_Parents) then
         File_Append_To_Theories
           (TFile.File, New_Custom_Declaration
              (Ada_Node  => Package_Entity,
               Domain    => EW_Prog,
               File_Name => NID (Full_Name (Package_Entity) & ".mlw")));
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

            File_Append_To_Theories
              (TFile.File, New_Custom_Declaration
                 (Domain    => EW_Prog,
                  File_Name =>
                    NID (Get_Generic_Name (Package_Entity,
                      List_Of_Entity.First (G_Parents)) & ".mlw"),
                  Subst     => Subst));

            Add_Dependencies (Package_Entity, G_Parents);

         end;
      end if;
   end Translate_Package_With_External_Axioms;

end Gnat2Why.External_Axioms;
