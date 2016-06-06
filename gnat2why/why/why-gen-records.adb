------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - R E C O R D S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2016, AdaCore                   --
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
with Common_Containers;          use Common_Containers;
with Elists;                     use Elists;
with Flow_Utility;               use Flow_Utility;
with GNAT.Source_Info;
with Gnat2Why.Expr;              use Gnat2Why.Expr;
with Namet;                      use Namet;
with Nlists;                     use Nlists;
with Sem_Aux;                    use Sem_Aux;
with Sem_Util;                   use Sem_Util;
with Sinfo;                      use Sinfo;
with Sinput;                     use Sinput;
with Snames;                     use Snames;
with SPARK_Definition;           use SPARK_Definition;
with Uintp;                      use Uintp;
with VC_Kinds;                   use VC_Kinds;
with Why.Atree.Accessors;        use Why.Atree.Accessors;
with Why.Atree.Builders;         use Why.Atree.Builders;
with Why.Atree.Modules;          use Why.Atree.Modules;
with Why.Conversions;            use Why.Conversions;
with Why.Gen.Decl;               use Why.Gen.Decl;
with Why.Gen.Expr;               use Why.Gen.Expr;
with Why.Gen.Names;              use Why.Gen.Names;
with Why.Gen.Preds;              use Why.Gen.Preds;
with Why.Gen.Progs;              use Why.Gen.Progs;
with Why.Gen.Terms;              use Why.Gen.Terms;
with Why.Inter;                  use Why.Inter;

package body Why.Gen.Records is

   --  For all Ada record types, we define a Why3 record type which contains
   --  all components of the Ada type, including discriminants, and including
   --  components in variant parts. We represent an Ada record as a Why3 record
   --  containing a record for discriminants, a record for other fields, and a
   --  boolean field for the 'Constrained attribute if needed. For tagged
   --  types, it also includes a field for the tag and one for the extension
   --  part representing components of derived types not visible in the current
   --  static type.

   --  For all such components, we then declare access program functions, where
   --  the precondition represents the discriminant check, and the
   --  postcondition states that the value of this function is just the value
   --  of the record component.

   --  The precondition for such access discriminant checks is actually
   --  separated out in a separate predicate. This predicate is generated
   --  for all types and subtypes. The declarations may be as follows:

   --    predicate y__check__pred (a : t) = a.x = 1
   --  ( to check that discriminant "x" is set to 1, and this is the check
   --  predicate for record field "y")

   --  Then we directly refer to that predicate in the program function:

   --    val rec__y_ (a : t)
   --    requires { y__check__pred (a) }

   --  For all record types which are not root types, we also define conversion
   --  functions to the root type (in logic space) and from the root type (in
   --  logic and program space).

   --  For all record types which are not root types, we define a check
   --  function, which checks whether its argument is in the current
   --  (sub-)type. This check function must be defined over the root type,
   --  otherwise it is not expressible or trivially true. This function is
   --  similar to the range_check functions in scalar/array types. In many
   --  cases, the subtype constraints are dynamic, so we cannot refer to them
   --  directly here. Instead, we take them as additional arguments:

   --  val range_check_ (x : base) (d1 : type_of_discr_1)
   --                              (d2 : type_of_discr_d2)
   --  requires { d1 = constr_of_first_discr /\ d2 = constr_of_second_discr }
   --  ensures  { result = x }

   --  For the implementation details: This is one place where we have to look
   --  at the declaration node to find which discriminant values imply the
   --  presence of which components. We traverse the N_Component_List of the
   --  type declaration, and for each component, and for each N_Variant_Part,
   --  we store a record of type [Component_Info] which contains the N_Variant
   --  node to which the component/variant part belongs, and the N_Variant_Part
   --  to which this N_Variant node belongs. In this way, we can easily access
   --  the discriminant (the Name of the N_Variant_Part) and the discrete
   --  choice (the Discrete_Choices of the N_Variant) of that component or
   --  variant part. For variant parts, the field [Ident] is empty, for
   --  components it contains the corresponding Why identifier.

   --  The map [Comp_Info] maps the component entities and N_Variant_Part nodes
   --  to their information record. This map is populated at the beginning of
   --  [Declare_Ada_Record].

   --  We ignore "completely hidden" components of derived record types (see
   --  also the discussion in einfo.ads and sem_ch3.adb)

   type Component_Info is record
      Parent_Variant  : Node_Id;
      Parent_Var_Part : Node_Id;
      Ident           : W_Identifier_Id;
   end record;

   package Info_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Component_Info,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   function Count_Fields_Not_In_Root (E : Entity_Id) return Natural;
   --  Counts the number of fields for the Why3 record representing type E that
   --  are not present in the representation of the root type for E.

   function Count_Root_Fields_Not_In_E (E, Root : Entity_Id) return Natural;
   --  Counts the number of fields for the Why3 record representing type Root
   --  that are not present in the representation of E.

   function Get_Rep_Record_Module (E : Entity_Id) return W_Module_Id;
   --  Return the name of a record's representative module.

   procedure Declare_Rep_Record_Type
     (P : W_Section_Id;
      E : Entity_Id);
   --  Emit all necessary Why3 declarations to support Ada records. This also
   --  supports variant records, private types and concurrent types.
   --  @param P the Why section to insert the declaration
   --  @param Theory the theory in which to insert the type declaration
   --  @param E the type entity to translate

   procedure Declare_Conversion_Check_Function
     (Section : W_Section_Id;
      E       : Entity_Id;
      Root    : Entity_Id);
   --  generate the program function which is used to insert subtype
   --  discriminant checks

   procedure Declare_Attributes
     (P       : W_Section_Id;
      E       : Entity_Id;
      Ty_Name : W_Name_Id);
   --  Declare functions for the record attributes

   procedure Declare_Component_Attributes
     (P : W_Section_Id;
      E : Entity_Id);
   --  Declare functions for the component attributes

   function Discriminant_Check_Pred_Name
     (E     : Entity_Id;
      Field : Entity_Id;
      Local : Boolean) return W_Identifier_Id;
   --  Given a record field, return the name of its discrimant check
   --  predicate. If Local is true, do not prefix the identifier.
   --  If the current record type is not a root type, return the name of the
   --  corresponding predicate in the root type module.

   function Get_Ancestor_Part_From_Root (R     : W_Expr_Id;
                                         Ty    : Entity_Id;
                                         Local : Boolean := False)
                                         return W_Expr_Id with
     Pre => Has_Private_Ancestor_Or_Root (Ty);
   --  @param R expression for a record
   --  @param Ty type for which we want to create an ancestor part
   --  @return The expression to be used for the ancestor part of a record of
   --  type Ty initialized from R.

   ------------------------------
   -- Count_Fields_Not_In_Root --
   ------------------------------

   function Count_Fields_Not_In_Root (E : Entity_Id) return Natural is
      Field : Node_Id;
      Count : Natural := 0;
   begin
      if Is_Record_Type (E) then
         Field := First_Component (E);
         while Present (Field) loop
            if not Is_Tag (Field)
              and then Component_Is_Visible_In_SPARK (Field)
              and then No (Root_Record_Component (Field))
            then
               Count := Count + 1;
            end if;
            Next_Component (Field);
         end loop;
      end if;

      return Count;
   end Count_Fields_Not_In_Root;

   --------------------------------
   -- Count_Root_Fields_Not_In_E --
   --------------------------------

   function Count_Root_Fields_Not_In_E (E, Root : Entity_Id) return Natural is
      Field : Node_Id;
      Count : Natural := 0;
   begin
      if Is_Record_Type (Root) then
         Field := First_Component (Root);
         while Present (Field) loop
            if not Is_Tag (Field)
              and then Component_Is_Visible_In_SPARK (Field)
              and then No (Search_Component_By_Name (E, Field))
            then
               Count := Count + 1;
            end if;
            Next_Component (Field);
         end loop;
      end if;

      return Count;
   end Count_Root_Fields_Not_In_E;

   -------------------------------
   -- Declare_Rep_Record_Theory --
   -------------------------------

   procedure Create_Rep_Record_Theory_If_Needed
     (P : W_Section_Id;
      E : Entity_Id)
   is
      Ancestor : constant Entity_Id :=
        Oldest_Parent_With_Same_Fields (E);
   begin
      --  Empty record types and clones do not require a representative
      --  theory.

      if Count_Why_Top_Level_Fields (E) = 0
        or else Record_Type_Is_Clone (E)
      then
         return;
      end if;

      --  If E has an ancestor with the same fields, use its representative.

      if Ancestor /= E then
         return;
      end if;

      Open_Theory
        (P, Get_Rep_Record_Module (E),
         Comment =>
           "Module for axiomatizing the record theory associated to type "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Declare_Rep_Record_Type (P, E);

      Close_Theory (P, Kind => Definition_Theory);
   end Create_Rep_Record_Theory_If_Needed;

   -----------------------------
   -- Declare_Rep_Record_Type --
   -----------------------------

   procedure Declare_Rep_Record_Type
     (P : W_Section_Id;
      E : Entity_Id)
   is
      procedure Declare_Record_Type;
      --  Declare the record type

      procedure Declare_Protected_Access_Functions;
      --  For each record field, declare an access program function, whose
      --  result is the same as the record field access, but there is a
      --  precondition (when needed).

      function Compute_Discriminant_Check (Field : Entity_Id) return W_Pred_Id;
      --  Compute the discriminant check for an access to the given field, as a
      --  predicate which can be used as a precondition.

      function Compute_Others_Choice
        (Info  : Component_Info;
         Discr : W_Term_Id) return W_Pred_Id;
      --  Compute (part of) the discriminant check for one discriminant in the
      --  special case where the N_Discrete_Choice is actually an
      --  N_Others_Choice.

      procedure Declare_Conversion_Functions;
      --  Generate conversion functions from this type to the root type, and
      --  back.

      procedure Declare_Equality_Function;
      --  Generate the boolean equality function for the record type

      function Discriminant_Check_Pred_Call
        (Field : Entity_Id;
         Arg   : W_Identifier_Id) return W_Pred_Id;
      --  Given a record field, return the a call to its discrimant check
      --  predicate, with the given argument. If that predicate is defined
      --  elsewhere (i.e. in the module for the root record type, prefix the
      --  call accordingly and add a conversion.

      procedure Init_Component_Info (E : Entity_Id)
        with Pre => Is_Record_Type (E);
      --  @param E record type
      --  For each subcomponent of E, create an entry in map Comp_Info

      procedure Init_Component_Info_For_Protected_Types (E : Entity_Id)
        with Pre => Is_Concurrent_Type (E);
      --  @param E the entity of the concurrent type
      --  For each component and discriminant of E, create an entry in map
      --  Comp_Info

      function Transform_Discrete_Choices
        (Case_N : Node_Id;
         Expr   : W_Term_Id) return W_Pred_Id;
      --  Wrapper for the function in Gnat2Why.Expr

      function Extract_Fun
        (Field       : Entity_Id;
         Is_Ancestor : Boolean;
         Local       : Boolean := True) return W_Identifier_Id;
      --  Returns the name of the extract function for an extension or an
      --  ancestor component.

      function Extract_Extension_Fun return W_Identifier_Id;
      --  Returns the name of the extract function for an extension component

      function Extract_Ancestor_Fun return W_Identifier_Id;
      --  Returns the name of the extract function for an ancestor component

      function Extract_Main_Fun (Is_Ancestor : Boolean) return W_Identifier_Id;
      --  Returns the name of the extract function for an ancestor component

      function New_Extension_Component_Expr (Ty : Entity_Id) return W_Expr_Id;
      --  Returns the name of the special field representing extension
      --  components.

      function New_Main_Component_Expr (Ty : Entity_Id) return W_Expr_Id;
      --  Returns the name of the special field representing invisible
      --  fields of a private type.

      ----------------------------------
      -- Declare_Extraction_Functions --
      ----------------------------------

      procedure Declare_Extraction_Functions_For_Ancestor;
      --  This is only called when the current tagged type has a private
      --  ancestor, so that the components of the root type are invisible
      --  in the current type.
      --
      --  For each component <comp> of the root type, declare a function
      --  extract__anc__<comp> to extract the value of the component from the
      --  ancestor field of a value of current type. Also declare a function
      --  hide_ext__ to generate the ancestor field of the current type based
      --  on the root components including its special extension field.
      --
      --  Note that we currently do not generate the axioms stating that
      --  extraction and hiding are inverse functions.

      procedure Declare_Extraction_Functions_For_Extension;
      --  For each extension component <comp> of the current type (i.e.
      --  a component that is not in the root type), declare a function
      --  extract__<comp> to extract the value of the component from the
      --  extension field of a value of root type. Also declare a function
      --  extract__ext__ to extract the value of the extension part for the
      --  current type, and a function hide_ext__ to generate the extension
      --  field of the root type based on the extension components and special
      --  extension field rec__ext__ of the current type.
      --
      --  Note that we currently do not generate the axioms stating that
      --  extraction and hiding are inverse functions, in the sense that:
      --
      --    root.rec_ext__ = hide_ext__ (extract__comp1 root.rec_ext__,
      --                                 extract__comp2 root.rec_ext__,
      --                                 ...
      --                                 extract__ext__ root.rec_ext__)
      --
      --  and for every extension component <comp> or the special extension
      --  component rec_ext__:
      --
      --    cur.comp = extract__comp (hide_ext__ (..., cur.comp, ...))
      --
      --  Previously, we generated axioms in Declare_Conversion_Functions that
      --  stated that converting back and forth between the current type and
      --  its root type is the identity in both directions. The axiom going
      --  from root to derived to root was incorrect in the case that the
      --  derived type had a constrained discriminant. These axioms are no
      --  longer generated.

      procedure Declare_Extraction_Functions
        (Components  : Node_Lists.List;
         Is_Ancestor : Boolean);
      --  Shared implementation for the two kinds of extraction functions, for
      --  ancestor components and extension components.
      --  @param Components The list of components to hide
      --  @param Is_Ancestor True if generating extraction functions for the
      --     ancestor component, False for the extension component

      Root      : constant Entity_Id := Root_Record_Type (E);
      Is_Root   : constant Boolean   := Root = E;
      Ty_Name   : constant W_Name_Id := To_Name (WNE_Rec_Rep);
      Abstr_Ty  : constant W_Type_Id := New_Named_Type (Name => Ty_Name);
      Comp_Info : Info_Maps.Map      := Info_Maps.Empty_Map;
      --  This map maps each component and each N_Variant node to a
      --  Component_Info record. This map is initialized by a call to
      --  Init_Component_Info;

      A_Ident  : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Abstr_Ty);
      R_Binder : constant Binder_Array :=
        (1 => (B_Name => A_Ident,
               others => <>));

      --------------------------------
      -- Compute_Discriminant_Check --
      --------------------------------

      function Compute_Discriminant_Check (Field : Entity_Id) return W_Pred_Id
      is
         Info : Component_Info :=
           Comp_Info.Element (Original_Record_Component (Field));
         Cond : W_Pred_Id := True_Pred;

      begin
         while Present (Info.Parent_Variant) loop
            declare
               Ada_Discr : constant Node_Id :=
                 Entity (Name (Info.Parent_Var_Part));
               R_Access  : constant W_Expr_Id :=
                 New_Record_Access
                   (Name  => +A_Ident,
                    Field => To_Ident (WNE_Rec_Split_Discrs));
               Discr     : constant W_Term_Id :=
                 +Insert_Conversion_To_Rep_No_Bool
                   (Domain => EW_Term,
                    Expr   => New_Record_Access
                      (Name  => R_Access,
                       Field => To_Why_Id (Ada_Discr, Local => Is_Root),
                       Typ   => EW_Abstract (Etype (Ada_Discr))));
               New_Cond  : constant W_Pred_Id :=
                 (if Is_Others_Choice (Discrete_Choices (Info.Parent_Variant))
                  then
                    Compute_Others_Choice (Info, Discr)
                  else
                    +Transform_Discrete_Choices
                      (Info.Parent_Variant, Discr));
            begin
               Cond :=
                 +New_And_Then_Expr
                   (Domain => EW_Pred,
                    Left   => +Cond,
                    Right  => +New_Cond);
               Info := Comp_Info.Element (Info.Parent_Var_Part);
            end;
         end loop;

         return Cond;
      end Compute_Discriminant_Check;

      ---------------------------
      -- Compute_Others_Choice --
      ---------------------------

      function Compute_Others_Choice (Info  : Component_Info;
                                      Discr : W_Term_Id) return W_Pred_Id
      is
         Var_Part : constant Node_Id := Info.Parent_Var_Part;
         Var      : Node_Id := First (Variants (Var_Part));
         Cond     : W_Pred_Id := True_Pred;

      begin
         while Present (Var) loop
            if not Is_Others_Choice (Discrete_Choices (Var)) then
               Cond :=
                 +New_And_Then_Expr
                   (Domain => EW_Pred,
                    Left   => +Cond,
                    Right  =>
                      New_Not
                        (Domain => EW_Pred,
                         Right  =>
                           +Transform_Discrete_Choices (Var, Discr)));
            end if;
            Next (Var);
         end loop;

         return Cond;
      end Compute_Others_Choice;

      ----------------------------------
      -- Declare_Conversion_Functions --
      ----------------------------------

      procedure Declare_Conversion_Functions is
         Num_Discrs      : constant Natural :=
           (if Has_Discriminants (E) then
              Natural (Number_Discriminants (E))
            else 0);
         Num_E_Fields    : constant Natural := Count_Why_Regular_Fields (E);
         Num_Root_Fields : constant Natural := Count_Why_Regular_Fields (Root);
         Is_Mutable_E    : constant Boolean :=
           not Is_Constrained (E)
           and then Has_Defaulted_Discriminants (E);
         Is_Mutable_Root : constant Boolean :=
           not Is_Constrained (Root)
           and then Has_Defaulted_Discriminants (Root);
         Num_E_All       : constant Natural := Count_Why_Top_Level_Fields (E);
         Num_Root_All    : constant Natural :=
           Count_Why_Top_Level_Fields (Root);
         To_Root_Aggr    : W_Field_Association_Array (1 .. Num_Root_All);
         From_Root_Aggr  : W_Field_Association_Array (1 .. Num_E_All);
         Seen            : Node_Sets.Set := Node_Sets.Empty_Set;
         From_Index      : Natural := 0;
         To_Index        : Natural := 0;

         R_Ident         : constant W_Identifier_Id :=
           New_Identifier (Name => "r", Typ => EW_Abstract (Root));
         From_Binder     : constant Binder_Array :=
           (1 => (B_Name => R_Ident,
                  others => <>));
      begin
         pragma Assert (Is_Tagged_Type (E) or else
                          (Num_E_All <= Num_Root_All));

         --  The current type may have components that are not present in the
         --  root type, corresponding to extensions of a tagged type. The root
         --  type may also have components that are not present in the current
         --  type, corresponding to hidden discriminants, as well as invisible
         --  components.

         --  When converting between the root type and the current type,
         --  components that are present in both types are simply copied
         --  (possibly with a conversion). Components from the target type
         --  that are not present in the source type are synthesized:

         --  . for an extension component <comp> when converting to the current
         --    type, call extract__<comp> on the extension field in the source
         --    value.

         --  . for the ancestor component rec__anc__ when converting to the
         --    current type, call hide_ancestor on all the ancestor fields in
         --    the source value.

         --  . for the extension component rec__ext__ when converting to the
         --    root type, call hide_extension on all the extension fields in
         --    the source value.

         --  . for a hidden root component <comp> when converting to the root
         --    type and the current type has a private ancestor, call
         --    extract__<comp> on the ancestor field in the source value.

         --  . for a hidden root component <comp> when converting to the root
         --    type and the current type has no private ancestors, generate
         --    a dummy value of its type, which should not be used.

         --  Step 1. Convert the __split_discrs field for discriminants

         --  Copy all discriminants between the root type and the current type,
         --  which should have exactly the same discriminants in SPARK.

         if Num_Discrs > 0 then
            declare
               Orig_D_Id      : constant W_Identifier_Id :=
                 E_Symb (Root, WNE_Rec_Split_Discrs);
               E_Discr_Access : constant W_Expr_Id :=
                 New_Record_Access (Name  => +A_Ident,
                                    Field => To_Ident (WNE_Rec_Split_Discrs));
               R_Discr_Access : constant W_Expr_Id :=
                 New_Record_Access (Name  => +R_Ident,
                                    Field => Orig_D_Id);
            begin

               From_Index := From_Index + 1;
               From_Root_Aggr (From_Index) :=
                 New_Field_Association
                   (Domain => EW_Term,
                    Field  => To_Ident (WNE_Rec_Split_Discrs),
                    Value  => R_Discr_Access);

               To_Index := To_Index + 1;
               To_Root_Aggr (To_Index) :=
                 New_Field_Association
                   (Domain => EW_Term,
                    Field  => Orig_D_Id,
                    Value  => E_Discr_Access);
            end;
         end if;

         --  Step 2. Convert the __split_fields field for components

         if Num_E_Fields > 0 or else Num_Root_Fields > 0 then
            declare
               To_Root_Field   :
                 W_Field_Association_Array (1 .. Num_Root_Fields);
               From_Root_Field :
                 W_Field_Association_Array (1 .. Num_E_Fields);
               Orig_F_Id       : constant W_Identifier_Id :=
                 E_Symb (Root, WNE_Rec_Split_Fields);
               E_Field_Access  : constant W_Expr_Id :=
                 New_Record_Access (Name  => +A_Ident,
                                    Field => To_Ident (WNE_Rec_Split_Fields));
               R_Field_Access  : constant W_Expr_Id :=
                 New_Record_Access (Name  => +R_Ident,
                                    Field => Orig_F_Id);
               Field           : Entity_Id := First_Component (E);

               Field_From_Index : Natural := 0;
               Field_To_Index   : Natural := 0;

            begin
               --  Step 2.1. Deal with components of the current type

               --  For each component of the current type, add an expression
               --  in From_Root_Field that either copies the root field or
               --  synthesizes a value for extension components, and add an
               --  expression in To_Root_Field that copies the current field,
               --  when present in the root type.
               --  Remark that, as array fields' bounds may depend on a
               --  disriminant, we must force no sliding for the conversion.

               while Present (Field) loop
                  if not Is_Tag (Field)
                    and then Component_Is_Visible_In_SPARK (Field)
                  then
                     declare
                        Orig     : constant Entity_Id :=
                          Root_Record_Component (Field);
                        Orig_Id  : W_Identifier_Id;
                        Field_Id : constant W_Identifier_Id :=
                          To_Why_Id (Field, Local => True);

                     begin
                        if Present (Orig) then
                           Orig_Id := To_Why_Id (Orig);

                           Field_From_Index := Field_From_Index + 1;
                           From_Root_Field (Field_From_Index) :=
                             New_Field_Association
                             (Domain => EW_Term,
                              Field  => Field_Id,
                              Value  =>
                                Insert_Simple_Conversion
                                (Domain => EW_Term,
                                 To     => EW_Abstract (Etype (Field)),
                                 Expr   =>
                                   New_Record_Access
                                   (Name  => R_Field_Access,
                                    Field => Orig_Id,
                                    Typ   => EW_Abstract (Etype (Orig))),
                                Force_No_Slide => True));

                           Field_To_Index := Field_To_Index + 1;
                           To_Root_Field (Field_To_Index) :=
                             New_Field_Association
                             (Domain => EW_Term,
                              Field  => Orig_Id,
                              Value  =>
                                Insert_Simple_Conversion
                                (Domain => EW_Term,
                                 To     => EW_Abstract (Etype (Orig)),
                                 Expr   =>
                                   New_Record_Access
                                   (Name  => E_Field_Access,
                                    Field => Field_Id,
                                    Typ   => EW_Abstract (Etype (Field))),
                                Force_No_Slide => True));

                           Seen.Include (Orig);

                        else
                           Field_From_Index := Field_From_Index + 1;
                           From_Root_Field (Field_From_Index) :=
                             New_Field_Association
                             (Domain => EW_Term,
                              Field  => Field_Id,
                              Value  =>
                                +W_Term_Id'(New_Call
                                  (Name =>
                                     Extract_Fun (Field, Is_Ancestor => False),
                                   Args =>
                                     (1 => New_Record_Access
                                        (Name  => R_Field_Access,
                                         Field =>
                                          +New_Extension_Component_Expr (Root),
                                         Typ   => EW_Private_Type)))));
                        end if;
                     end;
                  else
                     pragma Assert
                       (if not Component_Is_Visible_In_SPARK (Field)
                        then Has_Private_Ancestor_Or_Root (E)
                       or else Has_Private_Type (E) or else Is_Task_Type (E));
                  end if;

                  Next_Component (Field);
               end loop;

               --  Step 2.2. Deal with other components of the root type

               --  We should provide here a value for components of the root
               --  type which are not present in the current type. We use the
               --  'Seen' set to filter the components that have been added
               --  already. There are two cases:

               --  For invisible components due to a private ancestor of
               --  a tagged type, extract the components from the special
               --  ancestor fiels in the current type.

               --  Otherwise, hidden components correspond to a different
               --  variant from the one selected in the current type, and we
               --  add an expression in To_Root_Field that adds a dummy value
               --  of the corresponding type.

               --  Note that we don't need to deal with renamed discriminants,
               --  which would require reusing the value of the renaming,
               --  as these are not allowed in SPARK. Similarly, hidden
               --  discriminants cannot occur in SPARK.

               Field := First_Component (Root);
               while Present (Field) loop
                  if not Seen.Contains (Field)
                    and then Component_Is_Visible_In_SPARK (Field)
                  then
                     Field_To_Index := Field_To_Index + 1;
                     To_Root_Field (Field_To_Index) :=
                       New_Field_Association
                         (Domain => EW_Term,
                          Field  => To_Why_Id (Field),
                          Value  =>
                             (if Has_Private_Ancestor_Or_Root (E) then
                                +W_Term_Id'(New_Call
                                  (Name =>
                                     Extract_Fun (Field, Is_Ancestor => True),
                                   Args =>
                                     (1 => New_Record_Access
                                        (Name  => E_Field_Access,
                                         Field => To_Local
                                           (E_Symb (E, WNE_Rec_Ancestor))))))
                              else
                                Why_Default_Value
                                  (Domain => EW_Term,
                                   E      => Etype (Field))));
                  end if;
                  Next_Component (Field);
               end loop;

               --  Step 2.3. Deal with extension field for tagged types

               --  For tagged types, generate a value for the field
               --  representing extension components in the target type, based
               --  on the corresponding field from the source type, plus also
               --  extension components when targetting the root type.

               if Is_Tagged_Type (E) then
                  Field_From_Index := Field_From_Index + 1;
                  From_Root_Field (Field_From_Index) :=
                    New_Field_Association
                    (Domain => EW_Term,
                     Field  => To_Local (E_Symb (E, WNE_Rec_Extension)),
                     Value  =>
                       +W_Term_Id'(New_Call
                                     (Name => Extract_Extension_Fun,
                                      Args =>
                                        (1 => New_Record_Access
                                           (Name  => R_Field_Access,
                                            Field =>
                                              +New_Extension_Component_Expr
                                                (Root),
                                            Typ   => EW_Private_Type)))));

                  declare
                     Num_Args : constant Natural :=
                       Count_Fields_Not_In_Root (E)
                       + 1  --  for the extension field of the current type
                       + (if Has_Private_Ancestor_Or_Root (E) then 1 else 0)
                       + (if Has_Private_Type (E) or else Is_Task_Type (E)
                          then 1 else 0);
                     Args   : W_Expr_Array (1 .. Num_Args);
                     Index  : Natural := 0;
                     Field  : Node_Id := First_Component_Or_Discriminant (E);
                  begin
                     while Present (Field)
                     loop
                        if Is_Not_Hidden_Discriminant (Field)
                          and then not Is_Tag (Field)
                          and then No (Root_Record_Component (Field))
                          and then Component_Is_Visible_In_SPARK (Field)
                        then
                           Index := Index + 1;
                           Args (Index) :=
                             New_Record_Access
                             (Name  => E_Field_Access,
                              Field => To_Why_Id (Field, Local => True),
                              Typ   => EW_Abstract (Etype (Field)));
                        end if;
                        Next_Component_Or_Discriminant (Field);
                     end loop;

                     Index := Index + 1;
                     Args (Index) :=
                       New_Record_Access
                       (Name  => E_Field_Access,
                        Field => To_Local (E_Symb (E, WNE_Rec_Extension)),
                        Typ   => EW_Private_Type);

                     pragma Assert (Num_Args - Index in 0 .. 2);

                     if Has_Private_Type (E) or else Is_Task_Type (E) then
                        Index := Index + 1;
                        Args (Index) :=
                          New_Record_Access
                            (Name  => E_Field_Access,
                             Field => To_Local (E_Symb (E, WNE_Rec_Main)),
                             Typ   => EW_Private_Type);
                     end if;

                     pragma Assert (Num_Args - Index in 0 .. 1);

                     if Has_Private_Ancestor_Or_Root (E) then
                        Index := Index + 1;
                        Args (Index) :=
                          New_Record_Access
                            (Name  => E_Field_Access,
                             Field => To_Local (E_Symb (E, WNE_Rec_Ancestor)));
                     end if;

                     pragma Assert (Index = Num_Args);

                     Field_To_Index := Field_To_Index + 1;
                     To_Root_Field (Field_To_Index) :=
                       New_Field_Association
                       (Domain => EW_Term,
                        Field  => +New_Extension_Component_Expr (Root),
                        Value  => New_Call (Domain => EW_Term,
                                            Name   =>
                                              To_Ident (WNE_Hide_Extension),
                                            Args   => Args));
                  end;
               end if;

               --  Step 2.4. Deal with ancestor field for tagged types with a
               --  private ancestor

               if Has_Private_Ancestor_Or_Root (E) then
                     Field_From_Index := Field_From_Index + 1;
                     From_Root_Field (Field_From_Index) :=
                       New_Field_Association
                         (Domain => EW_Term,
                          Field  => To_Local (E_Symb (E, WNE_Rec_Ancestor)),
                          Value  =>
                            Get_Ancestor_Part_From_Root (+R_Ident, E, True));
               end if;

               --  Step 2.5. Deal with Rec__Main__ component for private types

               if Has_Private_Type (E) or else Is_Task_Type (E) then
                  Field_From_Index := Field_From_Index + 1;
                  if Is_Tagged_Type (E) then
                     From_Root_Field (Field_From_Index) :=
                       New_Field_Association
                         (Domain => EW_Term,
                          Field  => To_Local (E_Symb (E, WNE_Rec_Main)),
                          Value  =>
                            +W_Term_Id'(New_Call
                            (Name => Extract_Main_Fun (Is_Ancestor => False),
                             Args =>
                               (1 => New_Record_Access
                                  (Name  => R_Field_Access,
                                   Field =>
                                     +New_Extension_Component_Expr (Root),
                                   Typ   => EW_Private_Type)))));
                  else
                     From_Root_Field (Field_From_Index) :=
                       New_Field_Association
                         (Domain => EW_Term,
                          Field  => To_Local (E_Symb (E, WNE_Rec_Main)),
                          Value  => New_Record_Access
                                  (Name  => R_Field_Access,
                                   Field =>
                                     +New_Main_Component_Expr (Root),
                                   Typ   => EW_Private_Type));
                  end if;
               end if;

               if Has_Private_Type (Root) or else Is_Task_Type (Root) then
                  Field_To_Index := Field_To_Index + 1;
                  if Has_Private_Ancestor_Or_Root (E) then
                     To_Root_Field (Field_To_Index) :=
                       New_Field_Association
                         (Domain => EW_Term,
                          Field  => +New_Main_Component_Expr (Root),
                          Value  =>
                            +W_Term_Id'(New_Call
                            (Name => Extract_Main_Fun (Is_Ancestor => True),
                             Args =>
                               (1 => New_Record_Access
                                  (Name  => E_Field_Access,
                                   Field =>
                                      To_Local (E_Symb (E, WNE_Rec_Ancestor)),
                                   Typ   => EW_Private_Type)))));
                  else
                     To_Root_Field (Field_To_Index) :=
                       New_Field_Association
                         (Domain => EW_Term,
                          Field  => +New_Main_Component_Expr (Root),
                          Value  => New_Record_Access
                                  (Name  => E_Field_Access,
                                   Field =>
                                     To_Local (E_Symb (E, WNE_Rec_Main)),
                                   Typ   => EW_Private_Type));
                  end if;
               end if;

               if Num_E_Fields > 0 then
                  pragma Assert (Field_From_Index = From_Root_Field'Last);
                  From_Index := From_Index + 1;
                  From_Root_Aggr (From_Index) :=
                    New_Field_Association
                      (Domain => EW_Term,
                       Field  => To_Ident (WNE_Rec_Split_Fields),
                       Value  => New_Record_Aggregate
                         (Associations => From_Root_Field));
               end if;

               if Num_Root_Fields > 0 then
                  pragma Assert (Field_To_Index = To_Root_Field'Last);
                  To_Index := To_Index + 1;
                  To_Root_Aggr (To_Index) :=
                    New_Field_Association
                      (Domain => EW_Term,
                       Field  => Orig_F_Id,
                       Value  => New_Record_Aggregate
                         (Associations => To_Root_Field));
               end if;
            end;
         end if;

         --  Step 3. Copy or generate the attr__constrained field

         --  Step 3.1. Deal with the Constrained attribute of the current type

         --  If type E is not constrained and it has default discriminant
         --  values, then a value may be constrained or not, depending on
         --  whether it was declared with explicit values for the discriminants
         --  or not. Hence the Why3 type contains a field attr__constrained
         --  which must be copied between the root type and the current type.

         if Is_Mutable_E then
            pragma Assert (Is_Mutable_Root);

            From_Index := From_Index + 1;
            From_Root_Aggr (From_Index) :=
              New_Field_Association
                (Domain => EW_Term,
                 Field  => To_Ident (WNE_Attr_Constrained),
                 Value  =>
                   New_Record_Access
                     (Name => +R_Ident,
                      Field =>
                        +New_Attribute_Expr
                        (Root, EW_Term, Attribute_Constrained),
                      Typ   => EW_Bool_Type));

            To_Index := To_Index + 1;
            To_Root_Aggr (To_Index) :=
              New_Field_Association
                (Domain => EW_Term,
                 Field  =>
                   +New_Attribute_Expr (Root, EW_Term, Attribute_Constrained),
                 Value  =>
                   New_Record_Access
                     (Name  => +A_Ident,
                      Field => To_Ident (WNE_Attr_Constrained),
                      Typ   => EW_Bool_Type));

         --  Step 3.2. Deal with the Constrained attribute of the root type

         --  If type E is constrained or it does not have default discriminant
         --  values, then a value of type E is always constrained. The root
         --  type may still have a field attr__constrained however, in which
         --  case we set it to true.

         elsif Is_Mutable_Root then
            To_Index := To_Index + 1;
            To_Root_Aggr (To_Index) :=
              New_Field_Association
                (Domain => EW_Term,
                 Field  => +New_Attribute_Expr
                   (Root, EW_Term, Attribute_Constrained),
                 Value  => +True_Term);
         end if;

         --  Step 4. Copy the tag field of tagged types

         --  For tagged types, copy the tag field between the root type
         --  and the current type.

         if Is_Tagged_Type (E) then
            From_Index := From_Index + 1;
            From_Root_Aggr (From_Index) :=
              New_Field_Association
                (Domain => EW_Term,
                 Field  => To_Local (E_Symb (E, WNE_Attr_Tag)),
                 Value  =>
                   New_Record_Access
                     (Name  => +R_Ident,
                      Field => +New_Attribute_Expr
                        (Root, EW_Term, Attribute_Tag),
                      Typ   => EW_Int_Type));

            To_Index := To_Index + 1;
            To_Root_Aggr (To_Index) :=
              New_Field_Association
                (Domain => EW_Term,
                 Field  => +New_Attribute_Expr (Root, EW_Term, Attribute_Tag),
                 Value  =>
                   New_Record_Access
                     (Name  => +A_Ident,
                      Field => To_Local (E_Symb (E, WNE_Attr_Tag)),
                      Typ   => EW_Int_Type));
         end if;

         pragma Assert (To_Root_Aggr'Last = To_Index);
         pragma Assert (From_Root_Aggr'Last = From_Index);

         Emit
           (P,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Local (E_Symb (E, WNE_To_Base)),
               Binders     => R_Binder,
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type => EW_Abstract (Root),
               Def         =>
                 New_Record_Aggregate
                   (Associations => To_Root_Aggr)));
         Emit
           (P,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Local (E_Symb (E, WNE_Of_Base)),
               Binders     => From_Binder,
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         =>
                 New_Record_Aggregate
                   (Associations => From_Root_Aggr)));

      end Declare_Conversion_Functions;

      ----------------------------------
      -- Declare_Extraction_Functions --
      ----------------------------------

      procedure Declare_Extraction_Functions
        (Components  : Node_Lists.List;
         Is_Ancestor : Boolean)
      is
         X_Ident         : constant W_Identifier_Id :=
           New_Identifier (Name => "x", Typ => EW_Private_Type);
         Binder          : constant Binder_Array :=
           (1 => (B_Name => X_Ident,
                  others => <>));
         Hide_Name       : constant W_Identifier_Id :=
           (if Is_Ancestor then To_Local (E_Symb (E, WNE_Hide_Ancestor)) else
               To_Ident (WNE_Hide_Extension));
         Extract_Func    : constant W_Identifier_Id :=
           (if Is_Ancestor then
               Extract_Ancestor_Fun
            else
               Extract_Extension_Fun);
         Needs_Main      : constant Boolean :=
           (if Is_Ancestor then
               Has_Private_Type (Root) or else Is_Task_Type (Root)
            else Has_Private_Type (E) or else Is_Task_Type (E));
         Num_Hide_Params : constant Natural :=
           Natural (Components.Length)
           + 1  --  for the extension field of the current type
           + (if Needs_Main then 1 else 0)
           + (if not Is_Ancestor and then Has_Private_Ancestor_Or_Root (E)
              then 1 else 0);
         Hide_Binders    : Binder_Array (1 .. Num_Hide_Params);
         Index           : Natural := 0;

      begin
         --  the hide function to generate an ancestor field in E
         --  takes as arguments all components of the root type not
         --  present in E, plus the special extension, main, and
         --  ancestor components, if present in root.

         if Is_Ancestor then
            for Field of Components loop
               Index := Index + 1;
               Hide_Binders (Index) :=
                 (B_Name =>
                    New_Identifier (Name => Short_Name (Field),
                                    Typ => EW_Abstract (Etype (Field))),
                  others => <>);
            end loop;

            --  the extension field in the root type is also part of the
            --  ancestor field in E as it may contain some fields hidden in
            --  E.

            Index := Index + 1;
            Hide_Binders (Index) :=
              (B_Name => To_Local (E_Symb (Root, WNE_Rec_Extension)),
               others => <>);

            --  the main field of the root type is also part of the ancestor
            --  field of E

            if Needs_Main then
               Index := Index + 1;
               Hide_Binders (Index) :=
                 (B_Name => To_Local (E_Symb (Root, WNE_Rec_Main)),
                  others => <>);
            end if;

            --  the hide function to generate an extension field in the root
            --  type takes as arguments all components of E not present in the
            --  root type, plus the special extension, main, and
            --  ancestor components, if present in e.

         else
            for Field of Components loop
               Index := Index + 1;
               Hide_Binders (Index) :=
                 (B_Name =>
                    New_Identifier (Name => Short_Name (Field),
                                    Typ  => EW_Abstract (Etype (Field))),
                  others => <>);
            end loop;

            --  the extension field in the current type is also part of the
            --  extension field in the root type

            Index := Index + 1;
            Hide_Binders (Index) :=
              (B_Name => To_Local (E_Symb (E, WNE_Rec_Extension)),
               others => <>);

            --  the ancestor field in the current type is also part of
            --  the extension field in the root type, as some components
            --  of intermediate derived types may be represented in the
            --  ancestor field

            if Has_Private_Ancestor_Or_Root (E) then
               Index := Index + 1;
               Hide_Binders (Index) :=
                 (B_Name => To_Local (E_Symb (E, WNE_Rec_Ancestor)),
                  others => <>);
            end if;

            --  the main field of a private type is also part of the
            --  extension field in the root type

            if Needs_Main then
               Index := Index + 1;
               Hide_Binders (Index) :=
                 (B_Name => To_Local (E_Symb (E, WNE_Rec_Main)),
                  others => <>);
            end if;

            pragma Assert (Index = Num_Hide_Params);
         end if;

         --  function hide__ext__ (comp1 : typ1; .. ; x : __private)
         --                       : __private
         --    or
         --  function hide__anc__ (comp1 : typ1; .. ; x : __private)
         --                       : __private
         Emit (P,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => Hide_Name,
                  Binders     => Hide_Binders,
                  Labels      => Name_Id_Sets.Empty_Set,
                  Return_Type => EW_Private_Type));

         for Field of Components loop

            --  function extract__<comp> (x : __private) : <typ>
            --    or
            --  function extract_anc__<comp> (x : __private) : <typ>

            --  If an extraction function is already present in the base type
            --  or parent type of E, then the extraction function is a renaming
            --  of the base type's extraction function.

            declare
               Has_Definition : constant Boolean := not Is_Ancestor
                 and then Original_Record_Component (Field) /= Field;
               Definition     : constant W_Expr_Id :=
                 (if Has_Definition then
                     New_Call
                    (Domain   => EW_Term,
                     Name     =>
                       Extract_Fun (Original_Record_Component (Field),
                         Is_Ancestor, Local => False),
                     Binders  => Binder,
                     Typ      => EW_Abstract (Etype (Field)))
                  else Why_Empty);
            begin
               Emit (P,
                     New_Function_Decl
                       (Domain      => EW_Term,
                        Name        => Extract_Fun (Field, Is_Ancestor),
                        Binders     => Binder,
                        Labels      => Name_Id_Sets.Empty_Set,
                        Return_Type => EW_Abstract (Etype (Field)),
                        Def         => Definition));
            end;

            --  Declare an axiom for the extraction function stating:
            --  forall .... extract__<comp> (hide__ext (...)) = comp

            Emit (P,
                  New_Guarded_Axiom
                    (Name     =>
                       NID (Get_Name_String (Get_Symbol
                         (Get_Name (Extract_Fun (Field, Is_Ancestor))))
                         & "__conv"),
                     Binders  => Hide_Binders,
                     Def      => +New_Comparison
                       (Symbol => Why_Eq,
                        Left   => New_Call
                          (Domain  => EW_Term,
                           Name    => Extract_Fun (Field, Is_Ancestor),
                           Args    =>
                             (1 => New_Call
                                  (Domain  => EW_Term,
                                   Name    => Hide_Name,
                                   Binders => Hide_Binders,
                                   Typ     => EW_Private_Type)),
                           Typ     => EW_Abstract (Etype (Field))),
                        Right  => +New_Identifier
                          (Name => Short_Name (Field),
                           Typ  => EW_Abstract (Etype (Field))),
                        Domain => EW_Term)));

         end loop;

         if not Is_Ancestor then
            --  function extract__ext__ (x : __private) : __private
            Emit (P,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => Extract_Func,
                     Binders     => Binder,
                     Labels      => Name_Id_Sets.Empty_Set,
                     Return_Type => EW_Private_Type));
         end if;

         --  function extract__main__ (x : __private) : __private
         --    or
         --  function extract_anc__main__ (x : __private) : __private
         if Needs_Main then
            Emit (P,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => Extract_Main_Fun (Is_Ancestor),
                     Binders     => Binder,
                     Labels      => Name_Id_Sets.Empty_Set,
                     Return_Type => EW_Private_Type));
         end if;
      end Declare_Extraction_Functions;

      -----------------------------------------------
      -- Declare_Extraction_Functions_For_Ancestor --
      -----------------------------------------------

      procedure Declare_Extraction_Functions_For_Ancestor is
         Field : Entity_Id;
         Comps : Node_Lists.List;
      begin
         Field := First_Component (Root);

         while Present (Field) loop
            if not Is_Tag (Field)
              and then No (Search_Component_By_Name (E, Field))
              and then Component_Is_Visible_In_SPARK (Field)
            then
               Comps.Append (Field);
            end if;
            Next_Component (Field);
         end loop;

         Declare_Extraction_Functions (Components  => Comps,
                                       Is_Ancestor => True);
      end Declare_Extraction_Functions_For_Ancestor;

      ------------------------------------------------
      -- Declare_Extraction_Functions_For_Extension --
      ------------------------------------------------

      procedure Declare_Extraction_Functions_For_Extension is
         Field : Entity_Id;
         Comps : Node_Lists.List;
      begin
         Field := First_Component (E);

         while Present (Field) loop
            if not Is_Tag (Field)
              and then No (Root_Record_Component (Field))
              and then Component_Is_Visible_In_SPARK (Field)
            then
               Comps.Append (Field);
            end if;
            Next_Component (Field);
         end loop;

         Declare_Extraction_Functions (Components  => Comps,
                                       Is_Ancestor => False);
      end Declare_Extraction_Functions_For_Extension;

      -------------------------------
      -- Declare_Equality_Function --
      -------------------------------

      procedure Declare_Equality_Function is
         B_Ident : constant W_Identifier_Id :=
           New_Identifier (Name => "b", Typ => Abstr_Ty);
      begin
         if not Is_Limited_View (E) then
            declare
               Condition : W_Pred_Id := True_Pred;
               Comp      : Entity_Id := First_Component_Or_Discriminant (E);
            begin
               while Present (Comp) loop
                  if Is_Not_Hidden_Discriminant (Comp)
                    and then Component_Is_Visible_In_SPARK (Comp)
                  then
                     declare
                        Field_Ident    : constant W_Identifier_Id :=
                          To_Ident (if Ekind (Comp) = E_Discriminant
                                    then WNE_Rec_Split_Discrs
                                    else WNE_Rec_Split_Fields);
                        A_Access       : constant W_Expr_Id :=
                          New_Record_Access (Name  => +A_Ident,
                                             Field => Field_Ident);
                        B_Access       : constant W_Expr_Id :=
                          New_Record_Access (Name  => +B_Ident,
                                             Field => Field_Ident);
                        Field          : constant W_Identifier_Id :=
                          (if Is_Root or else Ekind (Comp) /= E_Discriminant
                           then To_Why_Id (Comp, Local => True)
                           else To_Why_Id (Comp, Rec => Root));
                        Comparison     : constant W_Pred_Id :=
                          +New_Ada_Equality
                          (Typ    => Retysp (Etype (Comp)),
                           Domain => EW_Pred,
                           Left   =>
                             New_Record_Access
                               (Name  => A_Access,
                                Field => Field,
                                Typ   => EW_Abstract (Etype (Comp))),
                           Right  =>
                             New_Record_Access
                               (Name  => B_Access,
                                Field => Field,
                                Typ   => EW_Abstract (Etype (Comp))),
                           Force_Predefined =>
                              not Is_Record_Type (Etype (Comp)));
                        Always_Present : constant Boolean :=
                          not (Has_Discriminants (E)) or else
                          Ekind (Comp) = E_Discriminant;
                     begin
                        Condition :=
                          +New_And_Then_Expr
                          (Domain => EW_Pred,
                           Left   => +Condition,
                           Right  =>
                             (if Always_Present then +Comparison
                              else
                                 New_Connection
                                (Domain => EW_Pred,
                                 Op     => EW_Imply,
                                 Left   =>
                                   +Discriminant_Check_Pred_Call
                                   (Comp, A_Ident),
                                 Right  => +Comparison)));
                     end;
                  end if;
                  Next_Component_Or_Discriminant (Comp);
               end loop;

               --  Equality of the invisible ancestor part

               if Has_Private_Ancestor_Or_Root (E) then
                  declare
                     Field_Ident : constant W_Identifier_Id :=
                       To_Ident (WNE_Rec_Split_Fields);
                     A_Access    : constant W_Expr_Id :=
                       New_Record_Access
                         (Name  => +A_Ident,
                          Field => Field_Ident);
                     B_Access    : constant W_Expr_Id :=
                       New_Record_Access
                         (Name  => +B_Ident,
                          Field => Field_Ident);
                     Comparison  : constant W_Pred_Id :=
                       +New_Comparison
                       (Symbol => Why_Eq,
                        Left   => New_Record_Access
                          (Name  => A_Access,
                           Field => To_Local (E_Symb (E, WNE_Rec_Ancestor)),
                           Typ   => EW_Private_Type),
                        Right  => New_Record_Access
                          (Name  => B_Access,
                           Field => To_Local (E_Symb (E, WNE_Rec_Ancestor)),
                           Typ   => EW_Private_Type),
                        Domain => EW_Pred);
                  begin
                     Condition :=
                       +New_And_Then_Expr
                       (Domain => EW_Pred,
                        Left   => +Condition,
                        Right  => +Comparison);
                  end;
               end if;

               --  Equality of the invisible private part

               if Has_Private_Type (E) then
                  declare
                     Field_Ident : constant W_Identifier_Id :=
                       To_Ident (WNE_Rec_Split_Fields);
                     A_Access    : constant W_Expr_Id :=
                       New_Record_Access
                         (Name  => +A_Ident,
                          Field => Field_Ident);
                     B_Access    : constant W_Expr_Id :=
                       New_Record_Access
                         (Name  => +B_Ident,
                          Field => Field_Ident);
                     Comparison  : constant W_Pred_Id :=
                       +New_Comparison
                       (Symbol => Why_Eq,
                        Left   => New_Record_Access
                          (Name  => A_Access,
                           Field => To_Local (E_Symb (E, WNE_Rec_Main)),
                           Typ   => EW_Private_Type),
                        Right  => New_Record_Access
                          (Name  => B_Access,
                           Field => To_Local (E_Symb (E, WNE_Rec_Main)),
                           Typ   => EW_Private_Type),
                        Domain => EW_Pred);
                  begin
                     Condition :=
                       +New_And_Then_Expr
                       (Domain => EW_Pred,
                        Left   => +Condition,
                        Right  => +Comparison);
                  end;
               end if;

               Emit
                 (P,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => To_Local (E_Symb (E, WNE_Bool_Eq)),
                     Binders     =>
                       R_Binder &
                       Binder_Array'(1 =>
                                         Binder_Type'(B_Name => B_Ident,
                                                      others => <>)),
                     Return_Type => +EW_Bool_Type,
                     Labels      => Name_Id_Sets.Empty_Set,
                     Def         =>
                       New_Conditional
                         (Domain    => EW_Term,
                          Condition => +Condition,
                          Then_Part => +True_Term,
                          Else_Part => +False_Term)));
            end;
         end if;

         Emit
           (P,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => New_Identifier (Name => "user_eq"),
               Return_Type => EW_Bool_Type,
               Binders     => R_Binder &
                 Binder_Array'(1 => Binder_Type'(B_Name => B_Ident,
                                                 others => <>)),
               Labels      => Name_Id_Sets.Empty_Set));

         --  Declare the dispatching equality function in root types
         if Is_Root and then Is_Tagged_Type (E) then
            Emit
              (P,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => To_Local (E_Symb (E, WNE_Dispatch_Eq)),
                  Return_Type => EW_Bool_Type,
                  Binders     => R_Binder &
                    Binder_Array'(1 => Binder_Type'(B_Name => B_Ident,
                                                    others => <>)),
                  Labels      => Name_Id_Sets.Empty_Set));
         end if;
      end Declare_Equality_Function;

      ----------------------------------------
      -- Declare_Protected_Access_Functions --
      ----------------------------------------

      procedure Declare_Protected_Access_Functions is
         Field : Entity_Id := First_Component_Or_Discriminant (E);
      begin

         --  ??? enrich the postcondition of access to discriminant, whenever
         --  we statically know its value (in case of E_Record_Subtype)

         while Present (Field) loop
            if Is_Not_Hidden_Discriminant (Field)
              and then Component_Is_Visible_In_SPARK (Field)
            then
               declare
                  Pred_Name : constant W_Identifier_Id :=
                    Discriminant_Check_Pred_Name (E, Field, True);
               begin

                  --  We generate a
                  --  discriminant check predicate. Unneeded for discriminants,
                  --  whose predicate is always "true.

                  --  ??? maybe only do that if the type has discriminants

                  if Ekind (Field) /= E_Discriminant then
                     declare
                        Pre_Cond  : constant W_Pred_Id :=
                          (if Ekind (Field) = E_Discriminant then True_Pred
                           else Compute_Discriminant_Check (Field));
                     begin
                        Emit (P,
                              New_Function_Decl
                                (Domain  => EW_Pred,
                                 Name    => Pred_Name,
                                 Binders => R_Binder,
                                 Labels  => Name_Id_Sets.Empty_Set,
                                 Def     => +Pre_Cond));
                     end;
                  end if;

                  --  In any case, we generate a program access function, whose
                  --  precondition is precisely the predicate. Note that
                  --  [Precond] has been computed so that it uses the correct
                  --  predicate name, whether it has been defined here or in
                  --  the root type. In the case of a discriminant, the
                  --  precondition is simply "true".

                  declare
                     Why_Name  : constant W_Identifier_Id :=
                       (if Is_Root or else Ekind (Field) /= E_Discriminant then
                             To_Why_Id (Field, Local => True)
                        else To_Why_Id (Field, Rec => Root));
                     Prog_Name : constant W_Identifier_Id :=
                       To_Program_Space (To_Why_Id (Field, Local => True));
                     R_Access  : constant W_Expr_Id :=
                       New_Record_Access
                         (Name  => +A_Ident,
                          Field =>
                            To_Ident
                              (if Ekind (Field) = E_Discriminant then
                                      WNE_Rec_Split_Discrs
                               else WNE_Rec_Split_Fields));
                     Post      : constant W_Pred_Id :=
                       New_Call
                         (Name => Why_Eq,
                          Typ  => EW_Bool_Type,
                          Args =>
                            (1 => +New_Result_Ident (Why_Empty),
                             2 =>
                               New_Record_Access
                                 (Name  => R_Access,
                                  Field => Why_Name)));
                     Precond   : constant W_Pred_Id :=
                       (if Ekind (Field) = E_Discriminant then True_Pred
                        else Discriminant_Check_Pred_Call (Field, A_Ident));
                  begin
                     Emit (P,
                           New_Function_Decl
                             (Domain      => EW_Prog,
                              Name        => Prog_Name,
                              Binders     => R_Binder,
                              Labels      => Name_Id_Sets.Empty_Set,
                              Return_Type =>
                                EW_Abstract (Etype (Field)),
                              Pre         => Precond,
                              Post        => Post));
                  end;
               end;
            end if;
            Next_Component_Or_Discriminant (Field);
         end loop;
      end Declare_Protected_Access_Functions;

      -------------------------
      -- Declare_Record_Type --
      -------------------------

      procedure Declare_Record_Type is
         Num_Discrs : constant Natural :=
           (if Has_Discriminants (E) then
              Natural (Number_Discriminants (E))
            else 0);
         Num_Fields : constant Natural := Count_Why_Regular_Fields (E);
         Is_Mutable : constant Boolean :=
           (not Is_Constrained (E)
            and then Has_Defaulted_Discriminants (E));
         Num_All    : constant Natural := Count_Why_Top_Level_Fields (E);

         Binders_D  : Binder_Array (1 .. Num_Discrs);
         Binders_F  : Binder_Array (1 .. Num_Fields);
         Binders_A  : Binder_Array (1 .. Num_All);
         Field      : Entity_Id := (if Has_Discriminants (E)
                                      or else Has_Unknown_Discriminants (E)
                                    then First_Discriminant (E)
                                    else Empty);
         Index      : Positive := 1;
         Index_All  : Positive := 1;

      begin
         --  Generate a record type for E's discriminants if E is a root type
         --  and use Root's record type for discriminants otherwise.

         if Num_Discrs > 0 then
            declare
               Discr_Name : constant W_Name_Id :=
                 To_Name (WNE_Rec_Split_Discrs);
            begin
               if Is_Root then
                  while Present (Field) loop
                     if Is_Not_Hidden_Discriminant (Field) then
                        Binders_D (Index) :=
                          (B_Name   =>
                             To_Why_Id
                               (Field,
                                Local => True,
                                Typ   => EW_Abstract (Etype (Field))),
                           Ada_Node => Field,
                           others   => <>);
                        Index := Index + 1;
                     end if;
                     Next_Discriminant (Field);
                  end loop;

                  Emit_Record_Declaration (Section => P,
                                           Name    => Discr_Name,
                                           Binders => Binders_D);

                  --  Generate a mutable record to hold elements of type
                  --  __split_discrs, as well as an havoc function for it.

                  Emit_Ref_Type_Definition (File => P,
                                            Name => Discr_Name);
                  Emit
                    (P,
                     New_Havoc_Declaration (Name => Discr_Name));
               end if;

               Binders_A (Index_All) :=
                 (B_Name =>
                    New_Identifier
                      (Ada_Node => Empty,
                       Name     => To_String (WNE_Rec_Split_Discrs),
                       Typ      =>
                         New_Type
                           (Type_Kind  => EW_Abstract,
                            Name       =>
                              (if not Is_Root then Get_Name
                                 (E_Symb (Root, WNE_Rec_Split_Discrs))
                               else Discr_Name),
                            Is_Mutable => False)),
                  others => <>);
               Index_All := Index_All + 1;
            end;
         end if;

         --  Generate a record type for E's normal components. This includes:
         --    . visible components of the type
         --    . invisible components and discriminants of a private ancestor
         --    . invisible components of a derived type

         if Num_Fields > 0
           or else Has_Private_Ancestor_Or_Root (E)
           or else Is_Tagged_Type (E)
         then
            Index := 1;
            if Is_Record_Type (E) or else Is_Protected_Type (E) then
               Field := First_Component (E);
               while Present (Field) loop
                  if not Is_Tag (Field)
                    and then Component_Is_Visible_In_SPARK (Field)
                  then
                     Binders_F (Index) :=
                       (B_Name   =>
                          To_Why_Id
                            (Field,
                             Local => True,
                             Typ   => EW_Abstract (Etype (Field))),
                        Ada_Node => Field,
                        others   => <>);
                     Index := Index + 1;
                  end if;
                  Next_Component (Field);
               end loop;
            end if;

            --  For private types, add a field of type __private representing
            --  the invisible components.

            if Has_Private_Type (E) or else Is_Task_Type (E) then
               Binders_F (Index) :=
                 (B_Name => To_Local (E_Symb (E, WNE_Rec_Main)),
                  others => <>);
               Index := Index + 1;
            end if;

            --  For types with a private ancestor, add a field of type
            --  __private representing the invisible ancestor components.

            if Has_Private_Ancestor_Or_Root (E) then
               Binders_F (Index) :=
                 (B_Name => To_Local (E_Symb (E, WNE_Rec_Ancestor)),
                  others => <>);
               Index := Index + 1;
            end if;

            --  For tagged types, add a field of type __private representing
            --  the unknown extension components.

            if Is_Tagged_Type (E) then
               Binders_F (Index) :=
                 (B_Name => To_Local (E_Symb (E, WNE_Rec_Extension)),
                  others => <>);
               Index := Index + 1;
            end if;

            if Is_Protected_Type (E) then
               for Part of Get_Part_Of_Variables (E) loop
                  Binders_F (Index) :=
                    (B_Name =>
                       To_Why_Id
                         (Part,
                          Local => True,
                          Typ   => EW_Abstract (Etype (Part))),
                     others => <>);
                  Index := Index + 1;
               end loop;
            end if;

            pragma Assert (Index = Binders_F'Last + 1);

            Emit_Record_Declaration (Section      => P,
                                     Name         =>
                                       To_Name (WNE_Rec_Split_Fields),
                                     Binders      => Binders_F,
                                     SPARK_Record => True);

            --  Generate a mutable record to hold elements of type
            --  __split_fields, as well as an havoc function for it.

            Emit_Ref_Type_Definition
              (File => P,
               Name => To_Name (WNE_Rec_Split_Fields));
            Emit
              (P,
               New_Havoc_Declaration (To_Name (WNE_Rec_Split_Fields)));

            Binders_A (Index_All) :=
              (B_Name =>
                 New_Identifier (Ada_Node => Empty,
                                 Name     => To_String (WNE_Rec_Split_Fields),
                                 Typ      =>
                                   New_Type
                                     (Type_Kind  => EW_Abstract,
                                      Name       =>
                                        To_Name (WNE_Rec_Split_Fields),
                                      Is_Mutable => False)),
               others => <>);
            Index_All := Index_All + 1;
         end if;

         --  Additional record field for records with mutable discriminants

         if Is_Mutable then
            Binders_A (Index_All) :=
              (B_Name =>
                 New_Identifier (Name => To_String (WNE_Attr_Constrained),
                                 Typ  => EW_Bool_Type),
               others => <>);
            Index_All := Index_All + 1;
         end if;

         --  For tagged types, add a tag field of type int

         if Is_Tagged_Type (E) then
            Binders_A (Index_All) :=
              (B_Name => To_Local (E_Symb (E, WNE_Attr_Tag)),
               others => <>);
            Index_All := Index_All + 1;
         end if;

         pragma Assert (Index_All = Num_All + 1);

         Emit_Record_Declaration (Section => P,
                                  Name    => Ty_Name,
                                  Binders => Binders_A);
      end Declare_Record_Type;

      ----------------------------------
      -- Discriminant_Check_Pred_Call --
      ----------------------------------

      function Discriminant_Check_Pred_Call
        (Field : Entity_Id;
         Arg   : W_Identifier_Id) return W_Pred_Id is
      begin
         return
           New_Call
             (Name => Discriminant_Check_Pred_Name (E, Field, True),
              Args => (1 => +Arg));
      end Discriminant_Check_Pred_Call;

      -----------------
      -- Extract_Fun --
      -----------------

      function Extract_Fun
        (Field       : Entity_Id;
         Is_Ancestor : Boolean;
         Local       : Boolean := True) return W_Identifier_Id
      is
         Prefix : constant Why_Name_Enum :=
           (if Is_Ancestor then WNE_Ancestor_Prefix else WNE_Extract_Prefix);
      begin
         return New_Identifier
           (Name   => To_String (Prefix) &
              Get_Name_String (Chars (Field)),
            Domain => EW_Term,
            Module =>
              (if Local then Why_Empty else E_Module (Scope (Field))));
      end Extract_Fun;

      ---------------------------
      -- Extract_Extension_Fun --
      ---------------------------

      function Extract_Extension_Fun return W_Identifier_Id is
      begin
         return New_Identifier (Name => To_String (WNE_Extract_Prefix) &
                                        To_String (WNE_Rec_Extension_Suffix));
      end Extract_Extension_Fun;

      --------------------------
      -- Extract_Ancestor_Fun --
      --------------------------

      function Extract_Ancestor_Fun return W_Identifier_Id is
      begin
         return New_Identifier (Name => To_String (WNE_Extract_Prefix) &
                                        To_String (WNE_Rec_Ancestor_Suffix));
      end Extract_Ancestor_Fun;

      ----------------------
      -- Extract_Main_Fun --
      ----------------------

      function Extract_Main_Fun (Is_Ancestor : Boolean) return W_Identifier_Id
      is
         Prefix : constant Why_Name_Enum :=
           (if Is_Ancestor then WNE_Ancestor_Prefix else WNE_Extract_Prefix);
      begin
         return New_Identifier (Name => To_String (Prefix) &
                                        To_String (WNE_Rec_Main_Suffix));
      end Extract_Main_Fun;

      ----------------------------------
      -- New_Extension_Component_Expr --
      ----------------------------------

      function New_Extension_Component_Expr (Ty : Entity_Id) return W_Expr_Id
      is
      begin
         return +E_Symb (Ty, WNE_Rec_Extension);
      end New_Extension_Component_Expr;

      -----------------------------
      -- New_Main_Component_Expr --
      -----------------------------

      function New_Main_Component_Expr (Ty : Entity_Id) return W_Expr_Id
      is
      begin
         return +E_Symb (Ty, WNE_Rec_Main);
      end New_Main_Component_Expr;

      -------------------------
      -- Init_Component_Info --
      -------------------------

      procedure Init_Component_Info (E : Entity_Id) is

         procedure Mark_Component_List
           (N               : Node_Id;
            Parent_Var_Part : Node_Id;
            Parent_Variant  : Node_Id);

         procedure Mark_Variant_Part
           (N               : Node_Id;
            Parent_Var_Part : Node_Id;
            Parent_Variant  : Node_Id);

         -------------------------
         -- Mark_Component_List --
         -------------------------

         procedure Mark_Component_List
           (N               : Node_Id;
            Parent_Var_Part : Node_Id;
            Parent_Variant  : Node_Id)
         is
            Field : Node_Id := First (Component_Items (N));
         begin
            while Present (Field) loop
               if Nkind (Field) /= N_Pragma then
                  Comp_Info.Insert
                    (Defining_Identifier (Field),
                     Component_Info'(
                       Parent_Variant  => Parent_Variant,
                       Parent_Var_Part => Parent_Var_Part,
                       Ident           =>
                         To_Why_Id
                           (Defining_Identifier (Field),
                            Local => True)));
               end if;
               Next (Field);
            end loop;
            if Present (Variant_Part (N)) then
               Mark_Variant_Part (Variant_Part (N),
                                  Parent_Var_Part,
                                  Parent_Variant);
            end if;
         end Mark_Component_List;

         -----------------------
         -- Mark_Variant_Part --
         -----------------------

         procedure Mark_Variant_Part
           (N               : Node_Id;
            Parent_Var_Part : Node_Id;
            Parent_Variant  : Node_Id)
         is
            Var : Node_Id := First (Variants (N));
         begin
            Comp_Info.Insert (N, Component_Info'(
              Parent_Variant  => Parent_Variant,
              Parent_Var_Part => Parent_Var_Part,
              Ident           => Why_Empty));
            while Present (Var) loop
               Mark_Component_List (Component_List (Var), N, Var);
               Next (Var);
            end loop;
         end Mark_Variant_Part;

         Decl_Node : constant Node_Id := Parent (E);
         Def_Node  : constant Node_Id :=
           (if Nkind (Decl_Node) = N_Full_Type_Declaration
            then Type_Definition (Decl_Node)
            else Empty);
         Discr : Node_Id :=
           (if Nkind (Decl_Node) in N_Full_Type_Declaration
            then First (Discriminant_Specifications (Decl_Node))
            else Empty);
         Components : constant Node_Id :=
           (if Present (Def_Node) then
              (case Nkind (Def_Node) is
                 when N_Record_Definition =>
                   Component_List (Def_Node),
                 when N_Derived_Type_Definition =>
                   (if Present (Record_Extension_Part (Def_Node)) then
                      Component_List (Record_Extension_Part (Def_Node))
                    else Empty),
                 when others =>
                   raise Program_Error)
            else Empty);
         Ancestor_Type : constant Entity_Id :=
           (if Full_View_Not_In_SPARK (E) then Get_First_Ancestor_In_SPARK (E)
            else Retysp (Etype (E)));

      --  Start of processing for Init_Component_Info

      begin
         while Present (Discr) loop
            Comp_Info.Insert
              (Defining_Identifier (Discr),
               Component_Info'
                 (Parent_Variant  => Empty,
                  Parent_Var_Part => Empty,
                  Ident           =>
                    To_Why_Id (Defining_Identifier (Discr), Local => True)));
            Next (Discr);
         end loop;

         if Present (Components) then
            Mark_Component_List (Components, Empty, Empty);
         end if;

         if Ancestor_Type /= E then
            Init_Component_Info (Ancestor_Type);
         end if;
      end Init_Component_Info;

      ---------------------------------------------
      -- Init_Component_Info_For_Protected_Types --
      ---------------------------------------------

      procedure Init_Component_Info_For_Protected_Types (E : Entity_Id) is
         Field : Entity_Id := First_Entity (E);
      begin
         while Present (Field) loop
            if Ekind (Field) in E_Discriminant | E_Component then
               Comp_Info.Insert
                 (Field,
                  Component_Info'(
                    Ident  =>
                      To_Why_Id (Field, Local => True),
                    others => Empty));
            end if;
            Next_Entity (Field);
         end loop;
      end Init_Component_Info_For_Protected_Types;

      --------------------------------
      -- Transform_Discrete_Choices --
      --------------------------------

      function Transform_Discrete_Choices
        (Case_N : Node_Id;
         Expr   : W_Term_Id) return W_Pred_Id is
      begin
         return +Gnat2Why.Expr.Transform_Discrete_Choices
           (Choices      => Discrete_Choices (Case_N),
            Choice_Type  => Empty,  --  not used for predicates, can be empty
            Matched_Expr => +Expr,
            Cond_Domain  => EW_Pred,
            Params       => Logic_Params);
      end Transform_Discrete_Choices;

   --  Start of processing for Declare_Ada_Record

   begin

      --  ??? rewrite with case statement
      if Ekind (E) in E_Record_Subtype | E_Record_Subtype_With_Private then
         Init_Component_Info (Retysp (Etype (E)));
      elsif Ekind (E) in E_Record_Type | E_Record_Type_With_Private then
         Init_Component_Info (E);
      elsif Ekind (E) in Concurrent_Kind then
         Init_Component_Info_For_Protected_Types (E);
      end if;

      Declare_Record_Type;

      --  We need to delare conversion functions before the protected access
      --  functions, because the former may be used in the latter

      if not Is_Root then
         if Has_Private_Ancestor_Or_Root (E) then
            --  The hiding of components from a private ancestor is only used
            --  for tagged types. For non-tagged types, components are repeated
            --  in the derived type.
            pragma Assert (Is_Tagged_Type (E));
            Declare_Extraction_Functions_For_Ancestor;
         end if;

         if Is_Tagged_Type (E) then
            Declare_Extraction_Functions_For_Extension;
         end if;

         Declare_Conversion_Functions;
      else
         --  Declare dummy conversion functions that will be used to convert
         --  other types which use E as a representative type.

         Emit
           (P,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Local (E_Symb (E, WNE_To_Base)),
               Binders     => R_Binder,
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         => +A_Ident));
         Emit
           (P,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Local (E_Symb (E, WNE_Of_Base)),
               Binders     => R_Binder,
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         => +A_Ident));
      end if;

      Declare_Protected_Access_Functions;
      Declare_Equality_Function;
      Declare_Attributes (P, E, Ty_Name);
      Declare_Component_Attributes (P, E);
   end Declare_Rep_Record_Type;

   ------------------------
   -- Declare_Ada_Record --
   ------------------------

   procedure Declare_Ada_Record
     (P : W_Section_Id;
      E : Entity_Id)
   is
      Root     : constant Entity_Id := Root_Record_Type (E);
      Is_Root  : constant Boolean   := Root = E;
      Ty_Name  : constant W_Name_Id := To_Why_Type (E, Local => True);
      Abstr_Ty : constant W_Type_Id := New_Named_Type (Name => Ty_Name);
      A_Ident  : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Abstr_Ty);
      R_Binder : constant Binder_Array :=
        (1 => (B_Name => A_Ident,
               others => <>));
      Rep_Module : constant W_Module_Id := Get_Rep_Record_Module (E);

   begin
      --  Get the empty record case out of the way

      if Count_Why_Top_Level_Fields (E) = 0 then

         --  Declare type for the empty record. If the type is not a root,
         --  then it is an alias of its root type.

         if Is_Root then
            Emit (P,
                  New_Type_Decl
                    (Name   => Ty_Name,
                     Labels => Name_Id_Sets.Empty_Set));
         else
            Emit (P,
                  New_Type_Decl
                    (Name  => Ty_Name,
                     Alias => EW_Abstract (Root)));
         end if;

         --  Conversion functions are identity

         declare
            R_Ident : constant W_Identifier_Id :=
              New_Identifier (Name => "r", Typ => (if Is_Root then Abstr_Ty
                                                   else EW_Abstract (Root)));
         begin
            Emit
              (P,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => To_Local (E_Symb (E, WNE_To_Base)),
                  Binders     => R_Binder,
                  Labels      => Name_Id_Sets.To_Set (NID ("inline")),
                  Return_Type => (if Is_Root then Abstr_Ty
                                  else EW_Abstract (Root)),
                  Def         => +A_Ident));
            Emit
              (P,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => To_Local (E_Symb (E, WNE_Of_Base)),
                  Binders     => Binder_Array'(1 => (B_Name => R_Ident,
                                                     others => <>)),
                  Labels      => Name_Id_Sets.To_Set (NID ("inline")),
                  Return_Type => Abstr_Ty,
                  Def         => +R_Ident));
         end;

         --  Equality function returns always true

         declare
            B_Ident : constant W_Identifier_Id :=
              New_Identifier (Name => "b", Typ => Abstr_Ty);
         begin

            Emit
              (P,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => To_Local (E_Symb (E, WNE_Bool_Eq)),
                  Binders     =>
                    R_Binder &
                    Binder_Array'(1 => Binder_Type'(B_Name => B_Ident,
                                                    others => <>)),
                  Return_Type => +EW_Bool_Type,
                  Labels      => Name_Id_Sets.To_Set (NID ("inline")),
                  Def         => +True_Term));
         end;

         Declare_Attributes (P, E, Ty_Name);

         return;
      end if;

      --  ??? We probably still need a way to tell that the right conversion
      --  function from this records subtype should go through the clone.

      if Record_Type_Is_Clone (E) then

         --  This type is simply a copy of an existing type, we re-export the
         --  corresponding module and generate trivial conversion functions,
         --  then return.

         declare
            Clone : constant Entity_Id := Record_Type_Cloned_Subtype (E);
         begin
            Add_Use_For_Entity (P, Clone, EW_Export, With_Completion => False);

            --  If the copy has the same name as the original, do not redefine
            --  the type name.

            if Short_Name (E) /= Short_Name (Clone) then
               Emit (P,
                     New_Type_Decl
                       (Name  => Ty_Name,
                        Alias =>
                          +New_Named_Type
                          (Name =>
                               To_Why_Type (Clone, Local => True))));
            end if;
         end;

         return;
      end if;

      --  Export the theory containing the record definition.

      Add_With_Clause (P, Rep_Module, EW_Export);

      --  Rename the representative record type as expected.

      Emit (P,
            New_Type_Decl
              (Name  => To_Why_Type (E, Local => True),
               Alias =>
                 +New_Named_Type
                   (Name => To_Name (WNE_Rec_Rep))));

      --  The static tag for the type is defined as a logic constant
      if Is_Tagged_Type (E) then
         Emit (P,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => To_Local (E_Symb (E, WNE_Tag)),
                  Labels      => Name_Id_Sets.Empty_Set,
                  Return_Type => EW_Int_Type));
      end if;

      if Root /= E
        and then Has_Discriminants (E)
        and then Is_Constrained (E)
      then
         Declare_Conversion_Check_Function (P, E, Root);
      end if;
   end Declare_Ada_Record;

   ------------------------
   -- Declare_Attributes --
   ------------------------

   procedure Declare_Attributes
     (P       : W_Section_Id;
      E       : Entity_Id;
      Ty_Name : W_Name_Id)
   is
      Abstr_Ty : constant W_Type_Id := New_Named_Type (Name => Ty_Name);
      A_Ident  : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Abstr_Ty);
      R_Binder : constant Binder_Array :=
        (1 => (B_Name => A_Ident,
               others => <>));
   begin

      --  The value size is defined as a logic constant

      Emit (P,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Local (E_Symb (E, WNE_Attr_Value_Size)),
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type => EW_Int_Type));

      --  The object size is defined as a logic function

      Emit (P,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Local (E_Symb (E, WNE_Attr_Object_Size)),
               Binders     => R_Binder,
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type => EW_Int_Type));

      --  Both value size and object size are non-negative

      --  The value alignement is defined as a logic constant

      Emit (P,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Local (E_Symb
                 (E, WNE_Attr_Value_Alignment)),
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type => EW_Int_Type));

      --  The object alignment is defined as a logic function

      Emit (P,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Local (E_Symb (E,
                 WNE_Attr_Object_Alignment)),
               Binders     => R_Binder,
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type => EW_Int_Type));

      --  Both value alignment and object alignment are non-negative

      declare
         Zero : constant W_Expr_Id :=
           New_Integer_Constant (Value => Uint_0);

         Value_Size_Fun : constant W_Expr_Id :=
           New_Call (Name   => To_Local (E_Symb (E, WNE_Attr_Value_Size)),
                     Domain => EW_Term,
                     Typ    => EW_Int_Type);

         Value_Size_Axiom : constant W_Pred_Id :=
           +New_Comparison (Symbol => Int_Infix_Ge,
                            Left   => Value_Size_Fun,
                            Right  => Zero,
                            Domain => EW_Term);

         Object_Size_Fun : constant W_Expr_Id :=
           New_Call (Name   =>
                       To_Local (E_Symb (E, WNE_Attr_Object_Size)),
                     Args   => (1 => +A_Ident),
                     Domain => EW_Term,
                     Typ    => EW_Int_Type);

         Object_Size_Pred : constant W_Pred_Id :=
           +New_Comparison (Symbol => Int_Infix_Ge,
                            Left   => Object_Size_Fun,
                            Right  => Zero,
                            Domain => EW_Term);

         Object_Size_Axiom : constant W_Pred_Id :=
           New_Universal_Quantif (Binders => R_Binder,
                                  Pred    => Object_Size_Pred);

         Value_Alignment_Fun : constant W_Expr_Id :=
           New_Call (Name     => To_Local (E_Symb
                     (E, WNE_Attr_Value_Alignment)),
                     Domain   => EW_Term,
                     Typ      => EW_Int_Type);

         Value_Alignment_Axiom : constant W_Pred_Id :=
           +New_Comparison (Symbol => Int_Infix_Ge,
                            Left   => Value_Alignment_Fun,
                            Right  => Zero,
                            Domain => EW_Term);

         Object_Alignment_Fun : constant W_Expr_Id :=
           New_Call (Name     =>
                       To_Local (E_Symb (E,
                         WNE_Attr_Object_Alignment)),
                     Args     => (1 => +A_Ident),
                     Domain   => EW_Term,
                     Typ      => EW_Int_Type);

         Object_Alignment_Pred : constant W_Pred_Id :=
           +New_Comparison (Symbol => Int_Infix_Ge,
                            Left   => Object_Alignment_Fun,
                            Right  => Zero,
                            Domain => EW_Term);

         Object_Alignment_Axiom : constant W_Pred_Id :=
           New_Universal_Quantif (Binders => R_Binder,
                                  Pred    => Object_Alignment_Pred);

      begin
         Emit (P,
               New_Axiom (Ada_Node => E,
                          Name     => NID ("value__size_axiom"),
                          Def      => Value_Size_Axiom));

         Emit (P,
               New_Axiom (Ada_Node => E,
                          Name     => NID ("object__size_axiom"),
                          Def      => Object_Size_Axiom));
         Emit (P,
               New_Axiom (Ada_Node => E,
                          Name     => NID ("value__alignment_axiom"),
                          Def      => Value_Alignment_Axiom));

         Emit (P,
               New_Axiom (Ada_Node => E,
                          Name     => NID ("object__alignment_axiom"),
                          Def      => Object_Alignment_Axiom));
      end;

   end Declare_Attributes;

   ----------------------------------
   -- Declare_Component_Attributes --
   ----------------------------------

   procedure Declare_Component_Attributes
     (P : W_Section_Id;
      E : Entity_Id)
   is
      Field : Entity_Id := First_Component_Or_Discriminant (E);

   begin
      while Present (Field) loop

         Emit (P,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        =>
                    To_Local (E_Symb (Field, WNE_Attr_First_Bit)),
                  Labels      => Name_Id_Sets.Empty_Set,
                  Return_Type => EW_Int_Type));

         Emit (P,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        =>
                    To_Local (E_Symb (Field, WNE_Attr_Last_Bit)),
                  Labels      => Name_Id_Sets.Empty_Set,
                  Return_Type => EW_Int_Type));

         Emit (P,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        =>
                    To_Local (E_Symb (Field, WNE_Attr_Position)),
                  Labels      => Name_Id_Sets.Empty_Set,
                  Return_Type => EW_Int_Type));
         declare
            Axiom : constant String := Short_Name (Field);

            Zero : constant W_Expr_Id :=
              New_Integer_Constant (Value => Uint_0);

            First_Bit_Fun : constant W_Expr_Id :=
              New_Call (Name   =>
                          To_Local (E_Symb (Field, WNE_Attr_First_Bit)),
                        Domain => EW_Term,
                        Typ    => EW_Int_Type);

            First_Bit_Axiom : constant W_Pred_Id :=
              +New_Comparison (Symbol => Int_Infix_Ge,
                               Left   => First_Bit_Fun,
                               Right  => Zero,
                               Domain => EW_Term);

            Last_Bit_Fun : constant W_Expr_Id :=
              New_Call (Name   =>
                          To_Local (E_Symb (Field, WNE_Attr_Last_Bit)),
                        Domain => EW_Term,
                        Typ    => EW_Int_Type);

            Last_Bit_Axiom : constant W_Pred_Id :=
              +New_Comparison (Symbol => Int_Infix_Gt,
                               Left   => Last_Bit_Fun,
                               Right  => First_Bit_Fun,
                               Domain => EW_Term);

            Position_Fun : constant W_Expr_Id :=
              New_Call (Name   =>
                          To_Local (E_Symb (Field, WNE_Attr_Position)),
                        Domain => EW_Term,
                        Typ    => EW_Int_Type);

            Position_Axiom : constant W_Pred_Id :=
              +New_Comparison (Symbol => Int_Infix_Ge,
                               Left   => Position_Fun,
                               Right  => Zero,
                               Domain => EW_Term);

         begin
            Emit (P,
                  New_Axiom (Ada_Node => Field,
                             Name     => NID (Axiom & "__first__bit_axiom"),
                             Def      => First_Bit_Axiom));

            Emit (P,
                  New_Axiom (Ada_Node => Field,
                             Name     => NID (Axiom & "__last__bit_axiom"),
                             Def      => Last_Bit_Axiom));
            Emit (P,
                  New_Axiom (Ada_Node => Field,
                             Name     => NID (Axiom & "__position_axiom"),
                             Def      => Position_Axiom));
         end;

         Next_Component_Or_Discriminant (Field);

      end loop;

   end Declare_Component_Attributes;

   ---------------------------------------
   -- Declare_Conversion_Check_Function --
   ---------------------------------------

   procedure Declare_Conversion_Check_Function
     (Section : W_Section_Id;
      E       : Entity_Id;
      Root    : Entity_Id)
   is
      Root_Name  : constant W_Name_Id := To_Why_Type (Root);
      Root_Abstr : constant W_Type_Id :=
        +New_Named_Type (Name => Root_Name);
      A_Ident    : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Root_Abstr);
      Num_Discr  : constant Natural :=
        (if Has_Discriminants (E) then
           Natural (Number_Discriminants (E))
         else 0);
      R_Access   : constant W_Expr_Id :=
        New_Record_Access (Name  => +A_Ident,
                           Field => E_Symb (Root, WNE_Rec_Split_Discrs));
      Discr      : Node_Id := First_Discriminant (E);
      Post       : constant W_Pred_Id :=
        New_Call
          (Name => Why_Eq,
           Typ  => EW_Bool_Type,
           Args => (+New_Result_Ident (Why_Empty), +A_Ident));
      R_Binder   : Binder_Array (1 .. Num_Discr + 1);
      Args       : W_Expr_Array (1 .. Num_Discr + 1);
      Check_Pred : W_Pred_Id := True_Pred;
      Count      : Natural := 1;
      Pre_Cond   : W_Pred_Id;
   begin
      R_Binder (Num_Discr + 1) :=
        Binder_Type'(B_Name => A_Ident,
                     others => <>);
      Args (Num_Discr + 1) := +A_Ident;
      Count := 1;
      Discr := First_Discriminant (E);
      while Present (Discr) loop
         if Is_Not_Hidden_Discriminant (Discr) then
            R_Binder (Count) :=
              Binder_Type'
                (B_Name =>
                   To_Why_Id
                     (Discr,
                      Local => True,
                      Typ => Base_Why_Type (Unique_Entity (Etype (Discr)))),
                 others => <>);
            Args (Count) := +To_Why_Id
              (Discr, Local => True,
               Typ => Base_Why_Type (Unique_Entity (Etype (Discr))));
            Check_Pred :=
              +New_And_Expr
              (Domain => EW_Pred,
               Left   => +Check_Pred,
               Right  =>
                 New_Call
                   (Domain => EW_Pred,
                    Name   => Why_Eq,
                    Typ    => EW_Bool_Type,
                    Args =>
                      (1 =>
                        +To_Why_Id
                        (Discr, Local => True,
                         Typ => Base_Why_Type (Unique_Entity (Etype (Discr)))),
                       2 =>
                         Insert_Simple_Conversion
                           (Domain   => EW_Term,
                            Expr     => New_Call
                              (Ada_Node => Root,
                               Name     => To_Why_Id (Discr, Rec => Root),
                               Args     => (1 => R_Access),
                               Domain   => EW_Term,
                               Typ      => EW_Abstract (Etype (Discr))),
                            To       =>
                              Base_Why_Type
                                (Unique_Entity (Etype (Discr)))))));
            Count := Count + 1;
         end if;
         Next_Discriminant (Discr);
      end loop;
      Emit (Section,
            New_Function_Decl
              (Domain  => EW_Pred,
               Name    => To_Local (E_Symb (E, WNE_Range_Pred)),
               Labels  => Name_Id_Sets.Empty_Set,
               Binders => R_Binder,
               Def     => +Check_Pred));
      Pre_Cond :=
        New_Call (Name => To_Local (E_Symb (E, WNE_Range_Pred)),
                  Args => Args);
      Emit (Section,
            New_Function_Decl
              (Domain      => EW_Prog,
               Name        => To_Local (E_Symb (E, WNE_Range_Check_Fun)),
               Binders     => R_Binder,
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type => Root_Abstr,
               Pre         => Pre_Cond,
               Post        => Post));
   end Declare_Conversion_Check_Function;

   ----------------------------------
   -- Discriminant_Check_Pred_Name --
   ----------------------------------

   function Discriminant_Check_Pred_Name
     (E     : Entity_Id;
      Field : Entity_Id;
      Local : Boolean) return W_Identifier_Id
   is
      Name : constant String := Short_Name (Field) & "__pred";
   begin
      if Local then
         return New_Identifier (Name => Name);
      else
         return New_Identifier
           (Domain   => EW_Pred,
            Ada_Node => E,
            Module   => E_Module (E),
            Name     => Name);
      end if;
   end Discriminant_Check_Pred_Name;

   ----------------------------------
   -- Field_Type_For_Discriminants --
   ----------------------------------

   function Field_Type_For_Discriminants (E : Entity_Id) return W_Type_Id is
     (New_Type (Ada_Node   => E,
                Is_Mutable => False,
                Type_Kind  => EW_Abstract,
                Name       =>
                   Get_Name (E_Symb (Unique_Entity (Root_Record_Type (E)),
                                     WNE_Rec_Split_Discrs))));

   ---------------------------
   -- Field_Type_For_Fields --
   ---------------------------

   function Field_Type_For_Fields (E : Entity_Id) return W_Type_Id is
     (New_Type (Ada_Node   => E,
                Is_Mutable => False,
                Type_Kind  => EW_Abstract,
                Name       =>
                   Get_Name (E_Symb (E, WNE_Rec_Split_Fields))));

   -----------------------------------------
   -- Generate_Associations_From_Ancestor --
   -----------------------------------------

   procedure Generate_Associations_From_Ancestor
     (Ada_Node     : Node_Id := Empty;
      Domain       : EW_Domain;
      Expr         : W_Expr_Id;
      Anc_Ty       : Entity_Id;
      Ty           : Entity_Id;
      Discr_Assocs : out W_Field_Association_Array;
      Field_Assocs : out W_Field_Association_Array)
   is
      Anc_Comp    : Entity_Id := First_Component_Or_Discriminant (Anc_Ty);
      Component   : Entity_Id;
      Discr_Index : Natural := 0;
      Field_Index : Natural := 0;
      Assoc       : W_Field_Association_Id;

   begin
      while Present (Anc_Comp) loop
         pragma Assert (Is_Not_Hidden_Discriminant (Anc_Comp));

         Component := Search_Component_By_Name (Ty, Anc_Comp);

         if Present (Component)
           and then Component_Is_Visible_In_SPARK (Component)
         then
            Assoc := New_Field_Association
              (Domain => Domain,
               Field  => To_Why_Id (Component),
               Value  => New_Ada_Record_Access
                 (Ada_Node => Ada_Node,
                  Domain   => (if Domain in EW_Prog | EW_Pterm then EW_Pterm
                               else EW_Term),
                  Name     => Expr,
                  Field    => Anc_Comp,
                  Ty       => Anc_Ty));

            if Ekind (Component) = E_Discriminant then
               Discr_Index := Discr_Index + 1;
               Discr_Assocs (Discr_Index) := Assoc;
            else
               Field_Index := Field_Index + 1;
               Field_Assocs (Field_Index) := Assoc;
            end if;

         else
            pragma Assert (Has_Private_Ancestor_Or_Root (Ty));
         end if;

         Next_Component_Or_Discriminant (Anc_Comp);
      end loop;

      if Has_Private_Ancestor_Or_Root (Ty) then
         Assoc := New_Field_Association
           (Domain => Domain,
            Field  => E_Symb (Ty, WNE_Rec_Ancestor),
            Value  => Get_Ancestor_Part_From_Root (Expr, Ty));

         Field_Index := Field_Index + 1;
         Field_Assocs (Field_Index) := Assoc;
      end if;

      --  All discriminants of the ancestor part should have been set, but
      --  possibly not all components in case of a discriminant record.

      pragma Assert (Discr_Index = Discr_Assocs'Last);
      pragma Assert (Field_Index = Field_Assocs'Last);
   end Generate_Associations_From_Ancestor;

   function Get_Ancestor_Part_From_Root (R     : W_Expr_Id;
                                         Ty    : Entity_Id;
                                         Local : Boolean := False)
                                         return W_Expr_Id
   is
      Root     : constant Entity_Id := Root_Record_Type (Ty);
      R_Fields : constant W_Expr_Id :=
        New_Fields_Access (Domain => EW_Term,
                           Name   =>
                             Insert_Simple_Conversion
                               (Domain => EW_Term,
                                Expr   => R,
                                To     => Type_Of_Node (Root)),
                           Ty     => Root);
      Num_Args : constant Natural :=
        Count_Root_Fields_Not_In_E (Ty, Root)
        + 1  --  for the extension field of the current type
        + (if Has_Private_Type (Root) or else Is_Task_Type (Root)
           then 1 else 0);
      Args     : W_Expr_Array (1 .. Num_Args);
      Index    : Natural := 0;
      Field    : Node_Id := First_Component_Or_Discriminant (Root);
   begin
      while Present (Field)
      loop
         if Is_Not_Hidden_Discriminant (Field)
           and then not Is_Tag (Field)
           and then No (Search_Component_By_Name (Ty, Field))
           and then Component_Is_Visible_In_SPARK (Field)
         then
            Index := Index + 1;
            Args (Index) :=
              New_Record_Access
                (Name  => R_Fields,
                 Field => To_Why_Id (Field),
                 Typ   => EW_Abstract (Etype (Field)));
         end if;
         Next_Component_Or_Discriminant (Field);
      end loop;

      Index := Index + 1;
      Args (Index) :=
        New_Record_Access
          (Name  => R_Fields,
           Field => E_Symb (Root, WNE_Rec_Extension),
           Typ   => EW_Private_Type);

      pragma Assert (Num_Args - Index in 0 .. 1);

      if Has_Private_Type (Root) or else Is_Task_Type (Root) then
         Index := Index + 1;
         Args (Index) :=
           New_Record_Access
             (Name  => R_Fields,
              Field => E_Symb (Root, WNE_Rec_Main),
              Typ   => EW_Private_Type);
      end if;

      pragma Assert (Index = Num_Args);

      return New_Call (Domain => EW_Term,
                       Name   =>
                         (if Local
                          then To_Local (E_Symb (Ty, WNE_Hide_Ancestor))
                          else E_Symb (Ty, WNE_Hide_Ancestor)),
                       Args   => Args);
   end Get_Ancestor_Part_From_Root;

   ---------------------------
   -- Get_Rep_Record_Module --
   ---------------------------

   function Get_Rep_Record_Module (E : Entity_Id) return W_Module_Id is
      Ancestor : constant Entity_Id :=
        Oldest_Parent_With_Same_Fields (E);
      Name     : constant String :=
        Full_Name (Ancestor) & To_String (WNE_Rec_Rep);

   begin
      return New_Module (File => No_Name,
                         Name => NID (Name));
   end Get_Rep_Record_Module;

   ---------------------------------------
   -- Insert_Subtype_Discriminant_Check --
   ---------------------------------------

   function Insert_Subtype_Discriminant_Check
     (Ada_Node : Node_Id;
      Check_Ty : Entity_Id;
      Expr     : W_Prog_Id) return W_Prog_Id
   is
      Root : constant Entity_Id := Root_Record_Type (Check_Ty);
   begin
      --  We make a last verification here to see whether a discriminant check
      --  is actually necessary.

      --  If the type does not have any discriminants, no check is needed
      --  obviously.

      if not Has_Discriminants (Check_Ty) then
         return Expr;
      end if;

      --  If the check type is a "root type", we cannot generate a check, as
      --  we do not have the appropriate predicate in Why3. However, the
      --  frontend always generates appropriate subtypes for discriminant
      --  records. As a consequence, we can only end up with the "root" type
      --  as a check type if we are in the case of a record type with default
      --  discriminants. But this case does not require checks.

      if Root = Check_Ty then
         return Expr;
      end if;

      --  The check type is not constrained, we don't have checks.

      if not Is_Constrained (Check_Ty) then
         return Expr;
      end if;

      return
        +New_VC_Call
        (Ada_Node => Ada_Node,
         Name     => Range_Check_Name (Check_Ty, RCK_Range),
         Progs    => Prepare_Args_For_Subtype_Check (Check_Ty, +Expr),
         Domain   => EW_Prog,
         Reason   => VC_Discriminant_Check,
         Typ      => Get_Type (+Expr));
   end Insert_Subtype_Discriminant_Check;

   ----------------------
   -- Insert_Tag_Check --
   ----------------------

   function Insert_Tag_Check
     (Ada_Node : Node_Id;
      Check_Ty : Entity_Id;
      Expr     : W_Prog_Id) return W_Prog_Id
   is
      Root  : constant Entity_Id := Root_Record_Type (Check_Ty);
      Id    : constant W_Expr_Id := New_Temp_For_Expr (+Expr);
      Call  : constant W_Expr_Id := New_Call
        (Ada_Node => Ada_Node,
         Domain   => EW_Pred,
         Name     => M_Main.Compat_Tags_Id,
         Args     =>
           (1 => New_Tag_Access (Domain => EW_Term,
                                 Name   => Id,
                                 Ty     => Root),
            2 => +E_Symb (E => Check_Ty,
                          S => WNE_Tag)),
         Typ      => EW_Bool_Type);
      --  Call Compat_Tags_Id on the object's tag and the type's tag
      Check : constant W_Prog_Id := New_Located_Assert
        (Ada_Node => Ada_Node,
         Pred     => +Call,
         Reason   => VC_Tag_Check,
         Kind     => EW_Assert);
   begin
      return +Binding_For_Temp (Domain  => EW_Prog,
                                Tmp     => Id,
                                Context => +Sequence
                                  (Left  => Check,
                                   Right => +Id));
   end Insert_Tag_Check;

   ---------------------------
   -- New_Ada_Record_Access --
   ---------------------------

   function New_Ada_Record_Access
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Field    : Entity_Id;
      Ty       : Entity_Id)
      return W_Expr_Id
   is
      Rec       : constant Entity_Id :=
        (if Ekind (Field) /= E_Discriminant then Ty
         else Root_Record_Type (Ty));
      Call_Id   : constant W_Identifier_Id := To_Why_Id (Field, Rec => Rec);
      Ret_Ty    : constant W_Type_Id :=
        (if Is_Part_Of_Protected_Object (Field) then
            EW_Abstract (Etype (Field))
         else
            EW_Abstract (Etype (Search_Component_By_Name (Ty, Field))));
      Top_Field : constant W_Expr_Id :=
        (if Ekind (Field) = E_Discriminant
         then New_Discriminants_Access (Ada_Node, Domain, Name, Ty)
         else New_Fields_Access (Ada_Node, Domain, Name, Ty));
   begin
      if Domain = EW_Prog and then
        Nkind (Ada_Node) /= N_Identifier and then
        Do_Discriminant_Check (Ada_Node)
      then
         return
           New_VC_Call
             (Ada_Node => Ada_Node,
              Name     => To_Program_Space (Call_Id),
              Progs    => (1 => Name),
              Domain   => Domain,
              Reason   => VC_Discriminant_Check,
              Typ      => Ret_Ty);

      else
         return
           New_Call
             (Ada_Node => Ada_Node,
              Name     => Call_Id,
              Args     => (1 => Top_Field),
              Domain   => Domain,
              Typ      => Ret_Ty);
      end if;
   end New_Ada_Record_Access;

   ------------------------------
   -- New_Ada_Record_Aggregate --
   ------------------------------

   function New_Ada_Record_Aggregate
     (Ada_Node     : Node_Id := Empty;
      Domain       : EW_Domain;
      Discr_Assocs : W_Field_Association_Array;
      Field_Assocs : W_Field_Association_Array;
      Ty           : Entity_Id) return W_Expr_Id
   is
      Num_All    : constant Natural := Count_Why_Top_Level_Fields (Ty);
      Num_Discr  : constant Natural :=
        (if Has_Discriminants (Ty)
         then Natural (Number_Discriminants (Ty))
         else 0);
      Num_Fields : constant Natural := Count_Why_Regular_Fields (Ty);
      Assoc      : W_Field_Association_Id;
      Assocs     : W_Field_Association_Array (1 .. Num_All);
      Index      : Natural := 0;
      Result     : W_Expr_Id;

   begin
      if Num_Discr > 0 then
         Assoc := New_Field_Association
           (Domain   => Domain,
            Field    => E_Symb (Ty, WNE_Rec_Split_Discrs),
            Value    => New_Record_Aggregate (Associations => Discr_Assocs));
         Index := Index + 1;
         Assocs (Index) := Assoc;
      end if;

      if Num_Fields > 0 then
         declare
            All_Field_Assocs : W_Field_Association_Array (1 .. Num_Fields);
            Num_Normal_Fields : constant Natural :=
              (if Is_Tagged_Type (Ty) then Num_Fields - 1 else Num_Fields);
         begin
            All_Field_Assocs (1 .. Num_Normal_Fields) := Field_Assocs;

            if Is_Tagged_Type (Ty) then
               All_Field_Assocs (Num_Fields) :=
                 New_Field_Association
                   (Domain => Domain,
                    Field  => E_Symb (Ty, WNE_Rec_Extension),
                    Value  => +M_Main.Null_Extension);
            end if;

            Assoc := New_Field_Association
              (Domain => Domain,
               Field  => E_Symb (Ty, WNE_Rec_Split_Fields),
               Value  => New_Record_Aggregate
                 (Associations => All_Field_Assocs));
            Index := Index + 1;
            Assocs (Index) := Assoc;
         end;
      end if;

      --  The Constrained attribute is never set, as the type of an aggregate
      --  is always a constrained type.

      pragma Assert (Is_Constrained (Ty));

      if Is_Tagged_Type (Ty) then
         Assoc := New_Field_Association
           (Domain => Domain,
            Field  => E_Symb (Ty, WNE_Attr_Tag),
            Value  => +E_Symb (Ty, WNE_Tag));
         Index := Index + 1;
         Assocs (Index) := Assoc;
      end if;

      Result := New_Record_Aggregate
        (Ada_Node     => Ada_Node,
         Associations => Assocs,
         Typ          => EW_Abstract (Ty));

      --  If the target type has a direct or inherited predicate, generate a
      --  corresponding check.

      if Domain = EW_Prog
        and then Has_Predicates (Ty)
      then
         Result := +Insert_Predicate_Check (Ada_Node => Ada_Node,
                                            Check_Ty => Ty,
                                            W_Expr   => +Result);
      end if;

      return Result;
   end New_Ada_Record_Aggregate;

   ------------------------------------
   -- New_Ada_Record_Check_For_Field --
   ------------------------------------

   function New_Ada_Record_Check_For_Field
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Field    : Entity_Id;
      Ty       : Entity_Id) return W_Expr_Id
   is
   begin
      return
        New_Call
          (Ada_Node => Ada_Node,
           Name     => Discriminant_Check_Pred_Name (Ty, Field, False),
           Args     => (1 => Name),
           Domain   => Domain,
           Typ      => EW_Bool_Type);
   end New_Ada_Record_Check_For_Field;

   ---------------------------
   -- New_Ada_Record_Update --
   ---------------------------

   function New_Ada_Record_Update
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Field    : Entity_Id;
      Value    : W_Expr_Id)
      return W_Expr_Id
   is
      Tmp         : constant W_Expr_Id := New_Temp_For_Expr (Name);
      Ty          : constant Entity_Id := Get_Ada_Node (+Get_Type (Name));
      Top_Field   : constant W_Expr_Id :=
        New_Fields_Access (Ada_Node, Domain, Tmp, Ty);
      Update_Expr : constant W_Expr_Id :=
        New_Fields_Update
          (Ada_Node => Ada_Node,
           Domain   => Domain,
           Name     => Tmp,
           Value    =>
             New_Record_Update
               (Ada_Node => Ada_Node,
                Name     => Top_Field,
                Updates  =>
                  (1 => New_Field_Association
                     (Domain => Domain,
                      Field  => To_Why_Id (Field, Domain, Rec => Ty),
                      Value  => Value))),
           Ty       => Ty);
      T           : W_Expr_Id;
   begin
      pragma Assert (Ekind (Field) /= E_Discriminant);
      if Domain = EW_Prog
        and then not Is_Protected_Component_Or_Discr_Or_Part_Of (Field)
      then
         T := +Sequence
           (+New_Ignore
              (Ada_Node => Ada_Node,
               Prog     =>
                 +New_Ada_Record_Access
                 (Ada_Node, Domain, Tmp, Field, Ty)),
            +Update_Expr);
      else
         T := Update_Expr;
      end if;
      return Binding_For_Temp (Ada_Node, Domain, Tmp, T);
   end New_Ada_Record_Update;

   ---------------------------
   -- New_Ada_Record_Update --
   ---------------------------

   function New_Ada_Record_Update
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Updates  : W_Field_Association_Array)
      return W_Expr_Id
   is
      Tmp         : constant W_Expr_Id := New_Temp_For_Expr (Name);
      Ty          : constant Entity_Id := Get_Ada_Node (+Get_Type (Name));
      Top_Field   : constant W_Expr_Id :=
        New_Fields_Access (Ada_Node, Domain, Tmp, Ty);
      Update_Expr : constant W_Expr_Id :=
        New_Fields_Update
          (Ada_Node => Ada_Node,
           Domain   => Domain,
           Name     => Tmp,
           Value    =>
             New_Record_Update
               (Ada_Node => Ada_Node,
                Name     => Top_Field,
                Updates  => Updates),
           Ty      => Ty);
   begin
      return Binding_For_Temp (Ada_Node, Domain, Tmp, Update_Expr);
   end New_Ada_Record_Update;

   ------------------------------
   -- New_Discriminants_Access --
   ------------------------------

   function New_Discriminants_Access
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Ty       : Entity_Id)
      return W_Expr_Id
   is
     (New_Call
        (Ada_Node => Ada_Node,
         Name     => E_Symb (Ty, WNE_Rec_Split_Discrs),
         Args     => (1 => Name),
         Domain   => Domain));

   ------------------------------
   -- New_Discriminants_Update --
   ------------------------------

   function New_Discriminants_Update
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Value    : W_Expr_Id;
      Ty       : Entity_Id)
      return W_Expr_Id
   is
     (New_Record_Update
        (Ada_Node => Ada_Node,
         Name     => Name,
         Updates  =>
           (1 => New_Field_Association
                (Domain => Domain,
                 Field  => E_Symb (Ty, WNE_Rec_Split_Discrs),
                 Value  => Value)),
         Typ      => EW_Abstract (Ty)));

   -----------------------
   -- New_Fields_Access --
   -----------------------

   function New_Fields_Access
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Ty       : Entity_Id)
      return W_Expr_Id
   is
     (New_Call
        (Ada_Node => Ada_Node,
         Name     => E_Symb (Ty, WNE_Rec_Split_Fields),
         Args     => (1 => Name),
         Domain   => Domain));

   -----------------------
   -- New_Fields_Update --
   -----------------------

   function New_Fields_Update
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Value    : W_Expr_Id;
      Ty       : Entity_Id)
      return W_Expr_Id
   is
     (New_Record_Update
        (Ada_Node => Ada_Node,
         Name     => Name,
         Updates  =>
           (1 => New_Field_Association
                (Domain => Domain,
                 Field  => E_Symb (Ty, WNE_Rec_Split_Fields),
                 Value  => Value)),
         Typ      => EW_Abstract (Ty)));

   -------------------------------
   -- New_Is_Constrained_Access --
   -------------------------------

   function New_Is_Constrained_Access
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Ty       : Entity_Id)
      return W_Expr_Id
   is
   begin
      if Has_Defaulted_Discriminants (Ty)
        and then not Is_Constrained (Ty)
      then
         return New_Call
           (Ada_Node => Ada_Node,
            Name     => +New_Attribute_Expr
              (Ty     => Ty,
               Domain => Domain,
               Attr   => Attribute_Constrained),
            Args     => (1 => Name),
            Domain   => Domain,
            Typ      => EW_Bool_Type);
      else
         return +True_Term;
      end if;
   end New_Is_Constrained_Access;

   ----------------------------------
   -- New_Record_Attributes_Update --
   ----------------------------------

   function New_Record_Attributes_Update
     (Ada_Node  : Node_Id := Empty;
      Domain    : EW_Domain;
      Name      : W_Expr_Id;
      From_Expr : W_Expr_Id := Why_Empty;
      Ty        : Entity_Id)
      return W_Expr_Id
   is
      Has_Constrained : constant Boolean :=
        Has_Defaulted_Discriminants (Ty)
        and then not Is_Constrained (Ty);
      --  If Ty has default discriminants and is not constrained then its
      --  'Constrained attribute should be preserved.

      Has_Tag         : constant Boolean :=
        (Is_Tagged_Type (Ty)
         and then (From_Expr /= Why_Empty
           or else not Is_Class_Wide_Type (Ty)));
      --  If Ty is tagged, its 'Tag attribute should be preserved except for
      --  defaults of classwide types.

      Num_Attr     : constant Natural :=
        (if Has_Constrained then (if Has_Tag then 2 else 1)
         else (if Has_Tag then 1 else 0));
      Associations : W_Field_Association_Array (1 .. Num_Attr);
      Index        : Positive := 1;

   begin
      if Num_Attr = 0 then
         return Name;
      end if;

      if Has_Constrained then
         declare
            Value : constant W_Expr_Id :=
              (if From_Expr = Why_Empty then +False_Term
               else New_Is_Constrained_Access
                 (Domain => Domain,
                  Name   => From_Expr,
                  Ty     => Ty));
         begin
            Associations (Index) :=
              New_Field_Association
                (Domain => Domain,
                 Field  => +New_Attribute_Expr
                   (Ty     => Ty,
                    Domain => Domain,
                    Attr   => Attribute_Constrained),
                 Value  => Value);
            Index := Index + 1;
         end;
      end if;

      if Has_Tag then
         declare
            Value : constant W_Expr_Id :=
              (if From_Expr = Why_Empty then
                  +E_Symb (E => Ty, S => WNE_Tag)
               else New_Tag_Access
                 (Domain => Domain,
                  Name   => From_Expr,
                  Ty     => Ty));
         begin
            Associations (Index) :=
              New_Field_Association
                (Domain => Domain,
                 Field  => +New_Attribute_Expr
                   (Ty     => Ty,
                    Domain => Domain,
                    Attr   => Attribute_Tag),
                 Value  => Value);
            Index := Index + 1;
         end;
      end if;

         return New_Record_Update
           (Ada_Node => Ada_Node,
            Name     => Name,
            Updates  => Associations,
            Typ      => Get_Type (Name));
   end New_Record_Attributes_Update;

   --------------------
   -- New_Tag_Access --
   --------------------

   function New_Tag_Access
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Ty       : Entity_Id)
      return W_Expr_Id
   is
   begin
      pragma Assert (Is_Tagged_Type (Ty));
      return New_Call
        (Ada_Node => Ada_Node,
         Name     => +New_Attribute_Expr
           (Ty     => Ty,
            Domain => Domain,
            Attr   => Attribute_Tag),
         Args     => (1 => Name),
         Domain   => Domain,
         Typ      => EW_Int_Type);
   end New_Tag_Access;

   ------------------------------------
   -- Oldest_Parent_With_Same_Fields --
   ------------------------------------

   function Oldest_Parent_With_Same_Fields (E : Entity_Id) return Entity_Id is
      Current  : Entity_Id := Retysp (E);
      Ancestor : Entity_Id := Current;

   begin
      --  Protected types and task types are not handled.

      if Ekind (Current) in Protected_Kind | Task_Kind then
         return E;
      end if;

      --  We do not handle types with discriminants yet which can have less
      --  fields than their parent.

      if Has_Discriminants (Current) then
         return Current;
      end if;

      --  If E is not tagged then the root type has the same fields as E.

      if not Is_Tagged_Type (Current) then
         return Root_Record_Type (Current);
      else

         --  Otherwise, we follow the Etype link until we find a type with
         --  more fields.

         loop

            --  If Current is private, its fullview is not in SPARK. Thus, it
            --  is considered to have private fields of its own.

            if Has_Private_Type (Current) then
               return Current;
            end if;

            --  Use the Etype field or the first ancestor in SPARK to get to
            --  parent type.
            --  Note that, even if Current is not a private type, its full
            --  view may still not be in SPARK, in particular when it is
            --  a (non-private) tagged derivation of a private type.

            if Full_View_Not_In_SPARK (Current) then
               Ancestor := Get_First_Ancestor_In_SPARK (Current);
            else
               Ancestor := Retysp (Etype (Current));
            end if;

            --  If we have found a type which is not a derived type, we are
            --  done.

            if Ancestor = Current then
               return Current;
            end if;

            --  If Current is not subtype, check whether it has more fields
            --  than Ancestor.

            if not (Ekind (Current) in SPARK_Util.Subtype_Kind) then
               declare
                  Field   : Entity_Id := First_Component (Current);
                  A_Field : Entity_Id;
               begin
                  while Present (Field) loop
                     A_Field := Search_Component_By_Name (Ancestor, Field);

                     --  If Field is not in Ancestor, we are done.

                     if No (A_Field) then
                        return Current;
                     end if;
                     Field := Next_Component (Field);
                  end loop;
               end;
            end if;

            Current := Ancestor;
         end loop;
      end if;
   end Oldest_Parent_With_Same_Fields;

   ------------------------------------
   -- Prepare_Args_For_Subtype_Check --
   ------------------------------------

   function Prepare_Args_For_Subtype_Check
     (Check_Ty : Entity_Id;
      Expr     : W_Expr_Id) return W_Expr_Array
   is
      Num_Discr : constant Natural :=
        (if Has_Discriminants (Check_Ty) then
           Natural (Number_Discriminants (Check_Ty))
         else 0);
      Args      : W_Expr_Array (1 .. Num_Discr + 1);
      Count     : Natural := 1;
      Discr     : Entity_Id := First_Discriminant (Check_Ty);
      Elmt      : Elmt_Id := First_Elmt (Stored_Constraint (Check_Ty));

   begin
      Args (Num_Discr + 1) := +Expr;
      while Present (Discr) loop
         if Is_Not_Hidden_Discriminant (Discr) then
            Args (Count) :=
              Transform_Expr
                (Domain => EW_Term,
                 Params => Logic_Params,
                 Expr   => Node (Elmt),
                 Expected_Type =>
                   Base_Why_Type (Unique_Entity (Etype (Discr))));
            Count := Count + 1;
            Next_Elmt (Elmt);
         end if;
         Next_Discriminant (Discr);
      end loop;

      return Args;
   end Prepare_Args_For_Subtype_Check;

   ----------------------------
   -- Record_From_Split_Form --
   ----------------------------

   function Record_From_Split_Form
     (Ada_Node : Node_Id := Empty;
      A        : W_Expr_Array;
      Ty       : Entity_Id)
      return W_Expr_Id
   is
      Associations : W_Field_Association_Array (A'Range);
      Index        : Positive := A'First;
   begin

      --  Store association for the top-level field for fields

      if Count_Why_Regular_Fields (Ty) > 0 then
         Associations (Index) := New_Field_Association
           (Domain   => EW_Term,
            Field    => E_Symb (Ty, WNE_Rec_Split_Fields),
            Value    => A (Index));
         Index := Index + 1;
      end if;

      --  Store association for the top-level field for discriminants

      if Has_Discriminants (Ty) then
         Associations (Index) := New_Field_Association
           (Domain   => EW_Term,
            Field    => E_Symb (Ty, WNE_Rec_Split_Discrs),
            Value    => A (Index));
         Index := Index + 1;
      end if;

      --  Store association for the 'Constrained attribute

      if not Is_Constrained (Ty) and then Has_Defaulted_Discriminants (Ty) then
         Associations (Index) := New_Field_Association
           (Domain => EW_Term,
            Field  => +New_Attribute_Expr (Ty     => Ty,
                                           Domain => EW_Term,
                                           Attr   => Attribute_Constrained),
            Value  => A (Index));
         Index := Index + 1;
      end if;

      --  Store association for the 'Tag attribute

      if Is_Tagged_Type (Ty) then
         Associations (Index) := New_Field_Association
           (Domain => EW_Term,
            Field  => +New_Attribute_Expr (Ty     => Ty,
                                           Domain => EW_Term,
                                           Attr   => Attribute_Tag),
            Value  => A (Index));
         Index := Index + 1;
      end if;

      return New_Record_Aggregate
        (Ada_Node     => Ada_Node,
         Associations => Associations,
         Typ          => EW_Abstract (Ty));
   end Record_From_Split_Form;

   ----------------------------
   -- Record_From_Split_Form --
   ----------------------------

   function Record_From_Split_Form (I : Item_Type; Ref_Allowed : Boolean)
                                    return W_Expr_Id
   is
      E      : constant Entity_Id :=
        (if I.Fields.Present then I.Fields.Binder.Ada_Node
         else I.Discrs.Binder.Ada_Node);
      Ty     : constant Entity_Id := I.Typ;
      Values : W_Expr_Array (1 .. Count_Why_Top_Level_Fields (Ty));
      Index  : Positive := 1;
   begin

      --  Store association for the top-level field for fields

      if I.Fields.Present then
         if Ref_Allowed then
            Values (Index) := New_Deref
              (E, I.Fields.Binder.B_Name, Get_Typ (I.Fields.Binder.B_Name));
         else
            Values (Index) := +I.Fields.Binder.B_Name;
         end if;
         Index := Index + 1;
      end if;

      --  Store association for the top-level field for discriminants

      if I.Discrs.Present then
         if I.Discrs.Binder.Mutable and then Ref_Allowed then
            Values (Index) := New_Deref
              (E, I.Discrs.Binder.B_Name, Get_Typ (I.Discrs.Binder.B_Name));
         else
            Values (Index) := +I.Discrs.Binder.B_Name;
         end if;
         Index := Index + 1;
      end if;

      --  Store association for the 'Constrained attribute

      if I.Constr.Present then
         Values (Index) := +I.Constr.Id;
         Index := Index + 1;
      end if;

      --  Store association for the 'Tag attribute

      if I.Tag.Present then
         Values (Index) := +I.Tag.Id;
         Index := Index + 1;
      end if;

      pragma Assert (Index = Values'Last + 1);

      return Record_From_Split_Form (E, Values, Ty);
   end Record_From_Split_Form;

   --------------------------------
   -- Record_Type_Cloned_Subtype --
   --------------------------------

   function Record_Type_Cloned_Subtype (E : Entity_Id) return Entity_Id is
      Result : Entity_Id := E;
   begin
      while Record_Type_Is_Clone (Result) loop

         --  Classwide types are translated as clones of their specific types

         if Ekind (Result) in E_Class_Wide_Type | E_Class_Wide_Subtype then
            Result := Retysp (Get_Specific_Type_From_Classwide (Result));

         --  Subtypes with a cloned_subtype with the same name are clones

         elsif Ekind (Result) = E_Record_Subtype
           and then Present (Cloned_Subtype (Result))
         then
            Result := Retysp (Cloned_Subtype (Result));

         --  Untagged private subtypes with no discriminants are clones

         elsif Ekind (Result) = E_Private_Subtype
           and then not Is_Tagged_Type (Result)
           and then not Has_Discriminants (Result)
         then
            Result := Retysp (Etype (Result));

         --   Result is not a cloned record type

         else
            raise Program_Error;
         end if;
      end loop;

      return Result;
   end Record_Type_Cloned_Subtype;

   --------------------------
   -- Record_Type_Is_Clone --
   --------------------------

   function Record_Type_Is_Clone (E : Entity_Id) return Boolean is
   begin

      --  Classwide types are translated as clones of their specific types

      if Ekind (E) in E_Class_Wide_Type | E_Class_Wide_Subtype then
         return True;

      --  Empty record types are not clones

      elsif Count_Why_Top_Level_Fields (E) = 0 then
         return False;

      --  Subtypes with a cloned_subtype with the same name are clones

      elsif Ekind (E) = E_Record_Subtype
        and then Present (Cloned_Subtype (E))
      then
         return True;

      --  Untagged private subtypes with no discriminants are clones

      elsif Ekind (E) = E_Private_Subtype
        and then not Is_Tagged_Type (E)
        and then not Has_Discriminants (E)
      then
         return True;
      else
         return False;
      end if;

      --  ??? We may be missing a case when a type is cloned twice and get the
      --  name of the first type back.
   end Record_Type_Is_Clone;

end Why.Gen.Records;
