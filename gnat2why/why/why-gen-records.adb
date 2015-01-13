------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - R E C O R D S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2015, AdaCore                   --
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

with Elists;              use Elists;
with Namet;               use Namet;
with Nlists;              use Nlists;
with Sem_Util;            use Sem_Util;
with Sinfo;               use Sinfo;
with Snames;              use Snames;

with SPARK_Definition;    use SPARK_Definition;
with VC_Kinds;            use VC_Kinds;

with Common_Containers;   use Common_Containers;

with Gnat2Why.Expr;       use Gnat2Why.Expr;
with Gnat2Why.Nodes;      use Gnat2Why.Nodes;

with Why.Atree.Accessors; use Why.Atree.Accessors;
with Why.Atree.Builders;  use Why.Atree.Builders;
with Why.Atree.Modules;   use Why.Atree.Modules;
with Why.Conversions;     use Why.Conversions;
with Why.Gen.Decl;        use Why.Gen.Decl;
with Why.Gen.Expr;        use Why.Gen.Expr;
with Why.Gen.Names;       use Why.Gen.Names;
with Why.Gen.Preds;       use Why.Gen.Preds;
with Why.Gen.Progs;       use Why.Gen.Progs;
with Why.Gen.Terms;       use Why.Gen.Terms;
with Why.Inter;           use Why.Inter;
with Why.Types;           use Why.Types;

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

   function Is_Not_Hidden_Discriminant (E : Entity_Id) return Boolean is
     (not (Ekind (E) = E_Discriminant and then Is_Completely_Hidden (E)));
   --  Opposite of Einfo.Is_Completely_Hidden, which also returns True if E is
   --  not a discriminant.

   function Count_Why_Record_Fields (E : Entity_Id) return Natural;
   --  Number of elements in the complete record type. It should contain:
   --    - A field __split_discrs for discriminants if E has at list one
   --    - A field __split_fields for components if E has at list one
   --    - A field attr__constrained if E's discriminants have defaults
   --    - A field __tag if E is tagged
   --  Note that tagged types have always at least one component, for the
   --  components of possible extensions.

   function Count_Fields_Not_In_Root (E : Entity_Id) return Natural;
   --  Counts the number of fields for the Why3 record representing type E that
   --  are not present in the representation of the root type for E.

   procedure Declare_Conversion_Check_Function
     (Theory : W_Theory_Declaration_Id;
      E      : Entity_Id;
      Root   : Entity_Id);
   --  generate the program function which is used to insert subtype
   --  discriminant checks

   function Discriminant_Check_Pred_Name
     (E     : Entity_Id;
      Field : Entity_Id;
      Local : Boolean) return W_Identifier_Id;
   --  Given a record field, return the name of its discrimant check
   --  predicate. If Local is true, do not prefix the identifier.
   --  If the current record type is not a root type, return the name of the
   --  corresponding predicate in the root type module.

   ------------------------------
   -- Count_Fields_Not_In_Root --
   ------------------------------

   function Count_Fields_Not_In_Root (E : Entity_Id) return Natural is
      Field : Node_Id := First_Component (E);
      Count : Natural := 0;
   begin
      while Present (Field) loop
         if not Is_Tag (Field)
           and then No (Root_Record_Component (Field))
         then
            Count := Count + 1;
         end if;
         Next_Component (Field);
      end loop;

      return Count;
   end Count_Fields_Not_In_Root;

   -----------------------------
   -- Count_Why_Record_Fields --
   -----------------------------

   function Count_Why_Record_Fields (E : Entity_Id) return Natural is
      Count : Natural := 0;
   begin
      --  Store discriminants in a separate sub-record field, so that
      --  subprograms that cannot modify discriminants are passed this
      --  sub-record by copy instead of by reference (with the split version
      --  of the record).

      if Number_Discriminants (E) > 0 then
         Count := Count + 1;
      end if;

      --  Store components in a separate sub-record field. This includes:
      --    . visible components of the type
      --    . invisible components and discriminants of a private ancestor
      --    . invisible components of a derived type

      if Count_Fields (E) > 0
        or else Has_Private_Ancestor (E)
        or else Is_Tagged_Type (E)
      then
         Count := Count + 1;
      end if;

      --  Directly store the attr__constrained and __tag fields in the record,
      --  as these fields cannot be modified after object creation.

      if not Is_Constrained (E) and then Has_Defaulted_Discriminants (E) then
         Count := Count + 1;
      end if;

      if Is_Tagged_Type (E) then
         Count := Count + 1;
      end if;

      return Count;
   end Count_Why_Record_Fields;

   -----------------------
   -- Declare_Ada_Record --
   -----------------------

   procedure Declare_Ada_Record
     (P       : Why_Section;
      Theory  : W_Theory_Declaration_Id;
      E       : Entity_Id)
   is
      procedure Declare_Attributes;
      --  Declare functions for the Size and Tag attributes

      procedure Declare_Record_Type;
      --  declare the record type

      procedure Declare_Protected_Access_Functions;
      --  for each record field, declare an access program function, whose
      --  result is the same as the record field access, but there is a
      --  precondition (when needed)

      function Compute_Discriminant_Check (Field : Entity_Id) return W_Pred_Id;
      --  compute the discriminant check for an access to the given field, as a
      --  predicate which can be used as a precondition

      function Compute_Others_Choice
        (Info  : Component_Info;
         Discr : W_Term_Id) return W_Pred_Id;
      --  compute (part of) the discriminant check for one discriminant in the
      --  special case where the N_Discrete_Choice is actually an
      --  N_Others_Choice

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

      function Transform_Discrete_Choices
        (Case_N : Node_Id;
         Expr   : W_Term_Id) return W_Pred_Id;
      --  Wrapper for the function in Gnat2Why.Expr;

      procedure Init_Component_Info (E : Entity_Id);
      --  Initialize the map which maps each component to its information
      --  record

      Root       : constant Entity_Id := Unique_Entity (Root_Record_Type (E));
      Is_Root    : constant Boolean   := Root = E;
      Ty_Name    : constant W_Name_Id := To_Why_Type (E, Local => True);
      Abstr_Ty   : constant W_Type_Id := New_Named_Type (Name => Ty_Name);
      Comp_Info  : Info_Maps.Map      := Info_Maps.Empty_Map;
      --  This map maps each component and each N_Variant node to a
      --  Component_Info record. This map is initialized by a call to
      --  Init_Component_Info;

      A_Ident    : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Abstr_Ty);
      R_Binder   : constant Binder_Array :=
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
                 +Insert_Simple_Conversion
                   (Domain => EW_Term,
                    Expr =>
                      New_Record_Access
                        (Name  => R_Access,
                         Field => To_Why_Id (Ada_Discr, Local => Is_Root),
                         Typ   => EW_Abstract (Etype (Ada_Discr))),
                    To   => EW_Int_Type);
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
      -- New_Extension_Component_Expr --
      ----------------------------------

      function New_Extension_Component_Expr (Ty : Entity_Id) return W_Expr_Id;
      --  Returns the name of the special field representing extension
      --  components.

      function New_Extension_Component_Expr (Ty : Entity_Id) return W_Expr_Id
      is
      begin
         return +Prefix (Ada_Node => Ty,
                         M        => E_Module (Ty),
                         W        => WNE_Rec_Extension,
                         Typ      => EW_Private_Type);
      end New_Extension_Component_Expr;

      -----------------
      -- Extract_Fun --
      -----------------

      function Extract_Fun
        (Field       : Entity_Id;
         Is_Ancestor : Boolean) return W_Identifier_Id;
      --  Returns the name of the extract function for an extension or an
      --  ancestor component.

      function Extract_Fun
        (Field       : Entity_Id;
         Is_Ancestor : Boolean) return W_Identifier_Id
      is
         Prefix : constant Why_Name_Enum :=
           (if Is_Ancestor then WNE_Ancestor_Prefix else WNE_Extract_Prefix);
      begin
         return New_Identifier (Name => To_String (Prefix) &
                                        Get_Name_String (Chars (Field)));
      end Extract_Fun;

      function Extract_Extension_Fun return W_Identifier_Id;
      --  Returns the name of the extract function for an extension component

      function Extract_Extension_Fun return W_Identifier_Id is
      begin
         return New_Identifier (Name => To_String (WNE_Extract_Prefix) &
                                        To_String (WNE_Rec_Extension_Suffix));
      end Extract_Extension_Fun;

      function Extract_Ancestor_Fun return W_Identifier_Id;
      --  Returns the name of the extract function for an ancestor component

      function Extract_Ancestor_Fun return W_Identifier_Id is
      begin
         return New_Identifier (Name => To_String (WNE_Extract_Prefix) &
                                        To_String (WNE_Rec_Ancestor_Suffix));
      end Extract_Ancestor_Fun;

      ------------------------
      -- Declare_Attributes --
      ------------------------

      procedure Declare_Attributes is
      begin
         --  The size is defined as a logic constant

         Emit (Theory,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => To_Ident (WNE_Attr_Size),
                  Labels      => Name_Id_Sets.Empty_Set,
                  Return_Type => EW_Int_Type));

         --  The static tag for the type is defined as a logic constant

         if Is_Tagged_Type (E) then
            Emit (Theory,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => To_Ident (WNE_Tag),
                     Labels      => Name_Id_Sets.Empty_Set,
                     Return_Type => EW_Int_Type));
         end if;
      end Declare_Attributes;

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

      procedure Declare_Extraction_Functions
        (Components  : Node_Lists.List;
         Is_Ancestor : Boolean)
      is
         X_Ident : constant W_Identifier_Id :=
           New_Identifier (Name => "x", Typ => EW_Private_Type);
         Binder : constant Binder_Array :=
           (1 => (B_Name => X_Ident,
                  others => <>));
         Hide_Name : constant Why_Name_Enum :=
           (if Is_Ancestor then WNE_Hide_Ancestor else WNE_Hide_Extension);
         Extract_Func : constant W_Identifier_Id :=
           (if Is_Ancestor then
               Extract_Ancestor_Fun
            else
               Extract_Extension_Fun);

      begin
         for Field of Components loop
            --  function extract__<comp> (x : __private) : <typ>
            --    or
            --  function extract_anc__<comp> (x : __private) : <typ>
            Emit (Theory,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => Extract_Fun (Field, Is_Ancestor),
                     Binders     => Binder,
                     Labels      => Name_Id_Sets.Empty_Set,
                     Return_Type => EW_Abstract (Etype (Field))));
         end loop;

         if not Is_Ancestor then
            --  function extract__ext__ (x : __private) : __private
            Emit (Theory,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => Extract_Func,
                     Binders     => Binder,
                     Labels      => Name_Id_Sets.Empty_Set,
                     Return_Type => EW_Private_Type));
         end if;

         declare
            Num_Hide_Params : constant Natural :=
              (if Is_Ancestor then
                  1
               else
                  Natural (Components.Length)
                  + 1  --  for the extension field of the current type
                  + (if Has_Private_Ancestor (E) then 1 else 0));

            Binder : Binder_Array (1 .. Num_Hide_Params);
            Index  : Natural := 0;

         begin
            --  the complete root object is argument to the hide function to
            --  generate the ancestor field in the current type

            if Is_Ancestor then
               Binder (1) :=
                 (B_Name =>
                    New_Identifier (Name => Short_Name (Root),
                                    Typ => EW_Abstract (Root)),
                  others => <>);

            --  the hide function to generate an extension field in the root
            --  type takes as arguments all components of the root type not
            --  present in the root type, plus the special extension and
            --  ancestor components, if present.

            else
               for Field of Components loop
                  Index := Index + 1;
                  Binder (Index) :=
                    (B_Name =>
                       New_Identifier (Name => Short_Name (Field),
                                       Typ => EW_Abstract (Etype (Field))),
                     others => <>);
               end loop;

               --  the extension field in the current type is also part of the
               --  extension field in the root type

               Index := Index + 1;
               Binder (Index) :=
                 (B_Name =>
                    New_Identifier (Name => To_String (WNE_Rec_Extension),
                                    Typ => EW_Private_Type),
                  others => <>);

               --  the ancestor field in the current type is also part of
               --  the extension field in the root type, as some components
               --  of intermediate derived types may be represented in the
               --  ancestor field

               if Has_Private_Ancestor (E) then
                  Index := Index + 1;
                  Binder (Index) :=
                    (B_Name =>
                       New_Identifier (Name => To_String (WNE_Rec_Ancestor),
                                       Typ => EW_Private_Type),
                     others => <>);
               end if;
            end if;

            --  function hide__ext__ (comp1 : typ1; .. ; x : __private)
            --                       : __private
            --    or
            --  function hide__anc__ (root : __private) : __private
            Emit (Theory,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => To_Ident (Hide_Name),
                     Binders     => Binder,
                     Labels      => Name_Id_Sets.Empty_Set,
                     Return_Type => EW_Private_Type));
         end;
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
            if not Is_Tag (Field) then
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
            then
               Comps.Append (Field);
            end if;
            Next_Component (Field);
         end loop;

         Declare_Extraction_Functions (Components  => Comps,
                                       Is_Ancestor => False);
      end Declare_Extraction_Functions_For_Extension;

      ----------------------------------
      -- Declare_Conversion_Functions --
      ----------------------------------

      procedure Declare_Conversion_Functions is
         Num_Discrs      : constant Natural := Number_Discriminants (E);
         Num_E_Fields    : constant Natural := Count_Fields (E);
         Num_Root_Fields : constant Natural := Count_Fields (Root);
         Is_Mutable_E    : constant Boolean :=
           not Is_Constrained (E)
           and then Has_Defaulted_Discriminants (E);
         Is_Mutable_Root : constant Boolean :=
           not Is_Constrained (Root)
           and then Has_Defaulted_Discriminants (Root);
         Num_E_All       : constant Natural := Count_Why_Record_Fields (E);
         Num_Root_All    : constant Natural := Count_Why_Record_Fields (Root);
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
         From_Ident     : constant W_Identifier_Id := To_Ident (WNE_Of_Base);

      begin
         pragma Assert (Is_Tagged_Type (E) or else
                          (Num_E_Fields <= Num_Root_Fields and then
                           Num_E_All <= Num_Root_All));

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
               To_Root_Discr   : W_Field_Association_Array (1 .. Num_Discrs);
               From_Root_Discr : W_Field_Association_Array (1 .. Num_Discrs);
               Orig_D_Id       : constant W_Identifier_Id :=
                 Prefix (E_Module (Root), WNE_Rec_Split_Discrs);
               E_Discr_Access : constant W_Expr_Id :=
                 New_Record_Access (Name  => +A_Ident,
                                    Field => To_Ident (WNE_Rec_Split_Discrs));
               R_Discr_Access : constant W_Expr_Id :=
                 New_Record_Access (Name  => +R_Ident,
                                    Field => Orig_D_Id);
               Field          : Entity_Id := First_Discriminant (E);
               Index          : Positive := 1;
            begin
               while Present (Field) loop
                  pragma Assert (Is_Not_Hidden_Discriminant (Field));
                  declare
                     Orig     : constant Entity_Id :=
                       Root_Record_Component (Field);
                     Orig_Id  : constant W_Identifier_Id :=
                       To_Why_Id (Orig);
                  begin
                     From_Root_Discr (Index) :=
                       New_Field_Association
                         (Domain => EW_Term,
                          Field  => Orig_Id,
                          Value  =>
                            Insert_Simple_Conversion
                              (Domain => EW_Term,
                               To     => EW_Abstract (Etype (Field)),
                               Expr   =>
                                 New_Record_Access
                                   (Name  => R_Discr_Access,
                                    Field => Orig_Id,
                                    Typ   => EW_Abstract (Etype (Orig)))));
                     To_Root_Discr (Index) :=
                       New_Field_Association
                         (Domain => EW_Term,
                          Field  => Orig_Id,
                          Value  =>
                            New_Record_Access
                              (Name  => E_Discr_Access,
                               Field => Orig_Id,
                               Typ   => EW_Abstract (Etype (Orig))));
                     Seen.Include (Orig);
                     Index := Index + 1;
                  end;
                  Next_Discriminant (Field);
               end loop;

               From_Index := From_Index + 1;
               From_Root_Aggr (From_Index) :=
                 New_Field_Association
                   (Domain => EW_Term,
                    Field  => To_Ident (WNE_Rec_Split_Discrs),
                    Value  => New_Record_Aggregate
                      (Associations => From_Root_Discr));

               To_Index := To_Index + 1;
               To_Root_Aggr (To_Index) :=
                 New_Field_Association
                   (Domain => EW_Term,
                    Field  => Orig_D_Id,
                    Value  => New_Record_Aggregate
                      (Associations => To_Root_Discr));
            end;
         end if;

         --  Step 2. Convert the __split_fields field for components

         if Num_E_Fields > 0 or Num_Root_Fields > 0 then
            declare
               To_Root_Field   :
               W_Field_Association_Array (1 .. Num_Root_Fields);
               From_Root_Field :
               W_Field_Association_Array (1 .. Num_E_Fields);
               Orig_F_Id       : constant W_Identifier_Id :=
                 Prefix (E_Module (Root), WNE_Rec_Split_Fields);
               E_Field_Access : constant W_Expr_Id :=
                 New_Record_Access (Name  => +A_Ident,
                                    Field => To_Ident (WNE_Rec_Split_Fields));
               R_Field_Access : constant W_Expr_Id :=
                 New_Record_Access (Name  => +R_Ident,
                                    Field => Orig_F_Id);
               Field          : Entity_Id := First_Component (E);
               Field_From_Index : Natural := 0;
               Field_To_Index   : Natural := 0;

            begin
               --  Step 2.1. Deal with components of the current type

               --  For each component of the current type, add an expression
               --  in From_Root_Field that either copies the root field or
               --  synthesizes a value for extension components, and add an
               --  expression in To_Root_Field that copies the current field,
               --  when present in the root type.

               while Present (Field) loop
                  if not Is_Tag (Field) then
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
                                    Typ   => EW_Abstract (Etype (Orig)))));

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
                                    Typ   => EW_Abstract (Etype (Field)))));

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
                  if not Seen.Contains (Field) then
                     Field_To_Index := Field_To_Index + 1;
                     To_Root_Field (Field_To_Index) :=
                       New_Field_Association
                         (Domain => EW_Term,
                          Field  => To_Why_Id (Field),
                          Value  =>
                             (if Has_Private_Ancestor (E) then
                                +W_Term_Id'(New_Call
                                  (Name =>
                                     Extract_Fun (Field, Is_Ancestor => True),
                                   Args =>
                                     (1 => New_Record_Access
                                        (Name  => E_Field_Access,
                                         Field => To_Ident (WNE_Rec_Ancestor),
                                         Typ   => EW_Private_Type))))
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
                     Field  => To_Ident (WNE_Rec_Extension),
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
                       + (if Has_Private_Ancestor (E) then 1 else 0);
                     Args   : W_Expr_Array (1 .. Num_Args);
                     Index  : Natural := 0;
                     Field  : Node_Id := First_Component_Or_Discriminant (E);
                  begin
                     while Present (Field) loop
                        if Is_Not_Hidden_Discriminant (Field)
                          and then not Is_Tag (Field)
                          and then No (Root_Record_Component (Field))
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
                        Field => To_Ident (WNE_Rec_Extension),
                        Typ   => EW_Private_Type);

                     pragma Assert (Num_Args - Index in 0 .. 1);

                     if Has_Private_Ancestor (E) then
                        Index := Index + 1;
                        Args (Index) :=
                          New_Record_Access
                            (Name  => E_Field_Access,
                             Field => To_Ident (WNE_Rec_Ancestor),
                             Typ   => EW_Private_Type);
                     end if;

                     pragma Assert (Index = Num_Args);

                     Field_To_Index := Field_To_Index + 1;
                     To_Root_Field (Field_To_Index) :=
                       New_Field_Association
                       (Domain => EW_Term,
                        Field  => +New_Extension_Component_Expr (Root),
                        Value  => New_Call (Domain => EW_Term,
                                            Name =>
                                              To_Ident (WNE_Hide_Extension),
                                            Args => Args));
                  end;
               end if;

               --  Step 2.4. Deal with ancestor field for tagged types with a
               --  private ancestor

               if Has_Private_Ancestor (E) then
                  Field_From_Index := Field_From_Index + 1;
                  From_Root_Field (Field_From_Index) :=
                    New_Field_Association
                      (Domain => EW_Term,
                       Field  => To_Ident (WNE_Rec_Ancestor),
                       Value  => New_Call (Domain => EW_Term,
                                           Name =>
                                             To_Ident (WNE_Hide_Ancestor),
                                           Args => (1 => +R_Ident)));
               end if;

               if Num_E_Fields > 0 then
                  From_Index := From_Index + 1;
                  From_Root_Aggr (From_Index) :=
                    New_Field_Association
                      (Domain => EW_Term,
                       Field  => To_Ident (WNE_Rec_Split_Fields),
                       Value  => New_Record_Aggregate
                         (Associations => From_Root_Field));
               end if;

               if Num_Root_Fields > 0 then
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
                        +New_Attribute_Expr (Root, Attribute_Constrained),
                      Typ   => EW_Bool_Type));

            To_Index := To_Index + 1;
            To_Root_Aggr (To_Index) :=
              New_Field_Association
                (Domain => EW_Term,
                 Field  =>
                   +New_Attribute_Expr (Root, Attribute_Constrained),
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
                 Field  => +New_Attribute_Expr (Root, Attribute_Constrained),
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
                 Field  => To_Ident (WNE_Attr_Tag),
                 Value  =>
                   New_Record_Access
                     (Name  => +R_Ident,
                      Field => +New_Attribute_Expr (Root, Attribute_Tag),
                      Typ   => EW_Int_Type));

            To_Index := To_Index + 1;
            To_Root_Aggr (To_Index) :=
              New_Field_Association
                (Domain => EW_Term,
                 Field  => +New_Attribute_Expr (Root, Attribute_Tag),
                 Value  =>
                   New_Record_Access
                     (Name  => +A_Ident,
                      Field => To_Ident (WNE_Attr_Tag),
                      Typ   => EW_Int_Type));
         end if;

         Emit
           (Theory,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Ident (WNE_To_Base),
               Binders     => R_Binder,
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type => EW_Abstract (Root),
               Def         =>
                 New_Record_Aggregate
                   (Associations => To_Root_Aggr)));
         Emit
           (Theory,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => From_Ident,
               Binders     => From_Binder,
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         =>
                 New_Record_Aggregate
                   (Associations => From_Root_Aggr)));

      end Declare_Conversion_Functions;

      -------------------------------
      -- Declare_Equality_Function --
      -------------------------------

      procedure Declare_Equality_Function is
         B_Ident   : constant W_Identifier_Id :=
           New_Identifier (Name => "b", Typ => Abstr_Ty);
         Condition : W_Pred_Id := True_Pred;
         Comp      : Entity_Id := First_Component_Or_Discriminant (E);
      begin
         while Present (Comp) loop
            if Is_Not_Hidden_Discriminant (Comp) then
               declare
                  A_Access  : constant W_Expr_Id :=
                    New_Record_Access
                      (Name  => +A_Ident,
                       Field =>
                         To_Ident
                           (if Ekind (Comp) = E_Discriminant then
                                   WNE_Rec_Split_Discrs
                            else WNE_Rec_Split_Fields));
                  B_Access  : constant W_Expr_Id :=
                    New_Record_Access
                      (Name  => +B_Ident,
                       Field =>
                         To_Ident
                           (if Ekind (Comp) = E_Discriminant then
                                   WNE_Rec_Split_Discrs
                            else WNE_Rec_Split_Fields));
                  Field      : constant W_Identifier_Id :=
                    (if Is_Root or else Ekind (Comp) /= E_Discriminant then
                          To_Why_Id (Comp, Local => True)
                     else To_Why_Id (Comp, Rec => Root));
                  Comparison : constant W_Pred_Id :=
                    +New_Ada_Equality
                    (Typ    => Unique_Entity (Etype (Comp)),
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
                             +Discriminant_Check_Pred_Call (Comp, A_Ident),
                           Right  => +Comparison)));
               end;
            end if;
            Next_Component_Or_Discriminant (Comp);
         end loop;
         Emit
           (Theory,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => To_Ident (WNE_Bool_Eq),
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
         Emit
           (Theory,
            New_Function_Decl
              (Domain      => EW_Term,
               Name        => New_Identifier (Name => "user_eq"),
               Return_Type => EW_Bool_Type,
               Binders     => R_Binder &
                 Binder_Array'(1                   =>
                                   Binder_Type'(B_Name => B_Ident,
                                                others => <>)),
               Labels      => Name_Id_Sets.Empty_Set));
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
            if Is_Not_Hidden_Discriminant (Field) then
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
                        Emit (Theory,
                              New_Function_Decl
                                (Domain => EW_Pred,
                                 Name   => Pred_Name,
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
                       New_Relation
                         (Left    => +New_Result_Ident (Why_Empty),
                          Op_Type => EW_Abstract,
                          Op      => EW_Eq,
                          Right   =>
                            New_Record_Access
                              (Name  => R_Access,
                               Field => Why_Name));
                     Precond   : constant W_Pred_Id :=
                       (if Ekind (Field) = E_Discriminant then True_Pred
                        else Discriminant_Check_Pred_Call (Field, A_Ident));
                  begin
                     Emit (Theory,
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
         Num_Discrs : constant Natural := Number_Discriminants (E);
         Num_Fields : constant Natural := Count_Fields (E);
         Is_Mutable : constant Boolean :=
           (not Is_Constrained (E)
            and then Has_Defaulted_Discriminants (E));
         Num_All    : constant Natural := Count_Why_Record_Fields (E);

         Binders_D  : Binder_Array (1 .. Num_Discrs);
         Binders_F  : Binder_Array (1 .. Num_Fields);
         Binders_A  : Binder_Array (1 .. Num_All);
         Field      : Entity_Id := First_Discriminant (E);
         Index      : Positive := 1;
         Index_All  : Positive := 1;
      begin

         --  Generate a record type for E's discriminants if E is a root type
         --  and use Root's record type for discriminants otherwise.

         if Num_Discrs > 0 then
            if Is_Root then
               while Present (Field) loop
                  if Is_Not_Hidden_Discriminant (Field) then
                     Binders_D (Index) :=
                       (B_Name =>
                          To_Why_Id
                            (Field,
                             Local => True,
                             Typ => EW_Abstract (Etype (Field))),
                        others => <>);
                     Index := Index + 1;
                  end if;
                  Next_Discriminant (Field);
               end loop;

               Emit (Theory,
                     New_Record_Definition
                       (Name    => To_Name (WNE_Rec_Split_Discrs),
                        Binders => Binders_D));
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
                           (if not Is_Root then To_Name
                              (Prefix (E_Module (Root), WNE_Rec_Split_Discrs))
                            else To_Name (WNE_Rec_Split_Discrs)),
                         Is_Mutable => False)),
               others => <>);
            Index_All := Index_All + 1;
         end if;

         --  Generate a record type for E's normal components. This includes:
         --    . visible components of the type
         --    . invisible components and discriminants of a private ancestor
         --    . invisible components of a derived type

         if Num_Fields > 0
           or else Has_Private_Ancestor (E)
           or else Is_Tagged_Type (E)
         then
            Index := 1;
            Field := First_Component (E);
            while Present (Field) loop
               if not Is_Tag (Field) then
                  Binders_F (Index) :=
                    (B_Name =>
                       To_Why_Id
                       (Field,
                        Local => True,
                        Typ => EW_Abstract (Etype (Field))),
                     others => <>);
                  Index := Index + 1;
               end if;
               Next_Component (Field);
            end loop;

            --  For types with a private ancestor, add a field of type
            --  __private representing the invisible ancestor components.

            if Has_Private_Ancestor (E) then
               Binders_F (Index) :=
                 (B_Name =>
                    New_Identifier (Name => To_String (WNE_Rec_Ancestor),
                                    Typ  => EW_Private_Type),
                  others => <>);
               Index := Index + 1;
            end if;

            --  For tagged types, add a field of type __private representing
            --  the unknown extension components.

            if Is_Tagged_Type (E) then
               Binders_F (Index) :=
                 (B_Name =>
                    New_Identifier (Name => To_String (WNE_Rec_Extension),
                                    Typ  => EW_Private_Type),
                  others => <>);
               Index := Index + 1;
            end if;

            Emit (Theory,
                  New_Record_Definition
                    (Name    => To_Name (WNE_Rec_Split_Fields),
                     Binders => Binders_F));

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
              (B_Name =>
                 New_Identifier (Name => To_String (WNE_Attr_Tag),
                                 Typ  => EW_Int_Type),
               others => <>);
            Index_All := Index_All + 1;
         end if;

         pragma Assert (Index_All = Num_All + 1);

         Emit (Theory,
           New_Record_Definition (Name    => Ty_Name,
                                  Binders => Binders_A));
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

      -------------------------
      -- Init_Component_Info --
      -------------------------

      procedure Init_Component_Info (E : Entity_Id) is

         procedure Mark_Component_List
           (N : Node_Id;
            Parent_Var_Part : Node_Id;
            Parent_Variant  : Node_Id);

         procedure Mark_Variant_Part
           (N : Node_Id;
            Parent_Var_Part : Node_Id;
            Parent_Variant  : Node_Id);

         --------------------------
         -- Mark_Component_Items --
         --------------------------

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

         Decl_Node  : constant Node_Id := Parent (E);
         Def_Node : constant Node_Id := Type_Definition (Decl_Node);
         Field : Node_Id := First (Discriminant_Specifications (Decl_Node));
         Components : constant Node_Id := Component_List (Def_Node);
         Extension_Components : constant Node_Id :=
           (if Nkind (Def_Node) = N_Derived_Type_Definition then
              Component_List (Record_Extension_Part (Def_Node))
            else Empty);

      --  Start of Init_Component_Info

      begin
         while Present (Field) loop
            Comp_Info.Insert
              (Defining_Identifier (Field),
               Component_Info'
                 (Parent_Variant  => Empty,
                  Parent_Var_Part => Empty,
                  Ident           =>
                    To_Why_Id (Defining_Identifier (Field),
                      Local => True)));
            Next (Field);
         end loop;

         if Present (Components) then
            Mark_Component_List (Components, Empty, Empty);
         end if;

         if Present (Extension_Components) then
            Mark_Component_List (Extension_Components, Empty, Empty);
         end if;

         if Underlying_Type (Etype (E)) /= E then
            Init_Component_Info (Underlying_Type (Etype (E)));
         end if;
      end Init_Component_Info;

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
            Index_Type   => Empty,
            Matched_Expr => +Expr,
            Cond_Domain  => EW_Pred,
            Params       => Logic_Params);
      end Transform_Discrete_Choices;

   --  Start of Declare_Ada_Record

   begin
      --  Get the empty record case out of the way

      if Count_Why_Record_Fields (E) = 0 then
         Emit (Theory,
               New_Type_Decl
                 (Name => Ty_Name,
                  Labels => Name_Id_Sets.Empty_Set));
         return;
      end if;

      --  ??? We probably still need a way to tell that the right conversion
      --  function from this records subtype should go through the clone.

      if Ekind (E) = E_Record_Subtype and then
        Present (Cloned_Subtype (E))
      then

         --  This type is simply a copy of an existing type, we re-export the
         --  corresponding module and generate trivial conversion functions,
         --  then return

         declare
            Clone : constant Entity_Id := Cloned_Subtype (E);
         begin
            Add_Use_For_Entity (P, Clone, EW_Export, With_Completion => False);

            --  if the copy has the same name as the original, do not redefine
            --  the type name.

            if Short_Name (E) /= Short_Name (Clone) then
               Emit (Theory,
                     New_Type_Decl
                       (Name => Ty_Name,
                        Alias =>
                          +New_Named_Type
                          (Name =>
                               To_Why_Type (Clone, Local => True))));
            end if;

            --  if the cloned type is a root type, or the private view of a
            --  root type, we need to define the conversion functions; in all
            --  other cases, they are already there.

            if Root_Record_Type (Clone) = MUT (Clone) then
               Emit
                 (Theory,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => To_Ident (WNE_To_Base),
                     Binders     => R_Binder,
                     Labels      => Name_Id_Sets.Empty_Set,
                     Return_Type => Abstr_Ty,
                     Def         => +A_Ident));
               Emit
                 (Theory,
                  New_Function_Decl
                    (Domain      => EW_Term,
                     Name        => To_Ident (WNE_Of_Base),
                     Binders     => R_Binder,
                     Labels      => Name_Id_Sets.Empty_Set,
                     Return_Type => Abstr_Ty,
                     Def         => +A_Ident));
            end if;
         end;

         return;
      end if;

      if Ekind (E) in E_Record_Subtype | E_Record_Subtype_With_Private then
         Init_Component_Info (Unique_Entity (Etype (E)));
      else
         Init_Component_Info (E);
      end if;

      Declare_Record_Type;

      --  We need to delare conversion functions before the protected access
      --  functions, because the former may be used in the latter

      if not Is_Root then
         if Has_Private_Ancestor (E) then
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
      end if;

      Declare_Protected_Access_Functions;
      Declare_Equality_Function;
      Declare_Attributes;

      if not Is_Root
        and then Has_Discriminants (E)
        and then Is_Constrained (E)
      then
         Declare_Conversion_Check_Function (Theory, E, Root);
      end if;
   end Declare_Ada_Record;

   ---------------------------------------
   -- Declare_Conversion_Check_Function --
   ---------------------------------------

   procedure Declare_Conversion_Check_Function
     (Theory : W_Theory_Declaration_Id;
      E      : Entity_Id;
      Root   : Entity_Id)
   is
      Root_Name  : constant W_Name_Id := To_Why_Type (Root);
      Root_Abstr : constant W_Type_Id :=
        +New_Named_Type (Name => Root_Name);
      A_Ident    : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Root_Abstr);
      Num_Discr  : constant Natural := Number_Discriminants (E);
      R_Access   : constant W_Expr_Id :=
        New_Record_Access (Name  => +A_Ident,
                           Field =>
                             Prefix (E_Module (Root), WNE_Rec_Split_Discrs));
      Discr      : Node_Id := First_Discriminant (E);
      Post       : constant W_Pred_Id :=
        New_Relation (Op      => EW_Eq,
                      Op_Type => EW_Abstract,
                      Left    => +New_Result_Ident (Why_Empty),
                      Right   => +A_Ident);
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
                 New_Relation
                   (Domain => EW_Pred,
                    Op      => EW_Eq,
                    Op_Type => EW_Int,
                    Left    => +To_Why_Id
                      (Discr, Local => True,
                       Typ => Base_Why_Type (Unique_Entity (Etype (Discr)))),
                    Right   =>
                      Insert_Simple_Conversion
                        (Domain   => EW_Term,
                         Expr     => New_Call
                           (Ada_Node => Root,
                            Name     => To_Why_Id (Discr, Rec => Root),
                            Args     => (1 => R_Access),
                            Domain   => EW_Term,
                            Typ      => EW_Abstract (Etype (Discr))),
                         To       =>
                           Base_Why_Type (Unique_Entity (Etype (Discr))))));
            Count := Count + 1;
         end if;
         Next_Discriminant (Discr);
      end loop;
      Emit (Theory,
            New_Function_Decl
              (Domain      => EW_Pred,
               Name        => To_Ident (WNE_Range_Pred),
               Labels      => Name_Id_Sets.Empty_Set,
               Binders     => R_Binder,
               Def         => +Check_Pred));
      Pre_Cond :=
        New_Call (Name   => To_Ident (WNE_Range_Pred),
                  Args   => Args);
      Emit (Theory,
            New_Function_Decl
              (Domain      => EW_Prog,
               Name        => To_Ident (WNE_Range_Check_Fun),
               Binders     => R_Binder,
               Labels      => Name_Id_Sets.Empty_Set,
               Return_Type => Root_Abstr,
               Pre         => Pre_Cond,
               Post        => Post));
   end Declare_Conversion_Check_Function;

   --------------------------
   -- Declare_Private_Type --
   --------------------------

   procedure Declare_Private_Type
     (Theory : W_Theory_Declaration_Id;
      E      : Entity_Id) is

      Root     : constant Entity_Id :=
        (if Fullview_Not_In_SPARK (E) then Get_First_Ancestor_In_SPARK (E)
         else E);
      Num_Discrs : constant Natural := Number_Discriminants (E);
      X_Binder : constant Binder_Type :=
        Binder_Type'(B_Name =>
                       New_Identifier (Name => "x",
                                       Typ  => EW_Private_Type),
                     others => <>);
      Y_Binder : constant Binder_Type :=
        Binder_Type'(B_Name =>
                       New_Identifier (Name => "y",
                                       Typ  => EW_Private_Type),
                     others => <>);
   begin

      --  We define a name for this type

      Emit (Theory,
            New_Type_Decl
              (New_Name (Symbol => NID (Short_Name (E))),
               Alias => EW_Private_Type));

      --  If E is a root type and has discriminants, declare a record type for
      --  its dicrimiants and an accessor for this record.

      if Root = E and then Num_Discrs > 0 then
         declare
            Index      : Positive := 1;
            Field      : Entity_Id := First_Discriminant (E);
            Binders_D  : Binder_Array (1 .. Num_Discrs);
         begin
            while Present (Field) loop
               if Is_Not_Hidden_Discriminant (Field) then
                  Binders_D (Index) :=
                    (B_Name =>
                       To_Why_Id
                         (Field,
                          Local => True,
                          Typ => EW_Abstract (Etype (Field))),
                     others => <>);
                  Index := Index + 1;
               end if;
               Next_Discriminant (Field);
            end loop;

            Emit (Theory,
                  New_Record_Definition
                    (Name    => To_Name (WNE_Rec_Split_Discrs),
                     Binders => Binders_D));
         end;

         Emit
           (Theory,
            Why.Gen.Binders.New_Function_Decl
              (Ada_Node    => E,
               Domain      => EW_Term,
               Name        => To_Ident (WNE_Rec_Split_Discrs),
               Return_Type =>
                 New_Type
                   (Type_Kind  => EW_Abstract,
                    Name       =>
                      To_Name (WNE_Rec_Split_Discrs),
                    Is_Mutable => False),
               Labels      => Name_Id_Sets.Empty_Set,
               Binders     => (1 => X_Binder)));
      end if;

      --  If E has mutable discriminants, declare an accessor to its
      --  is_constrained field.

      if Has_Defaulted_Discriminants (E) and then
        not Is_Constrained (E)
      then
         Emit
           (Theory,
            Why.Gen.Binders.New_Function_Decl
              (Ada_Node    => E,
               Domain      => EW_Term,
               Name        => To_Ident (WNE_Attr_Constrained),
               Return_Type => EW_Bool_Type,
               Labels      => Name_Id_Sets.Empty_Set,
               Binders     => (1 => X_Binder)));
      end if;

      if Has_Discriminants (E) and then Root /= E then
         Declare_Conversion_Check_Function (Theory => Theory,
                                            E      => E,
                                            Root   => Root);
      end if;

      Emit
        (Theory,
         Why.Gen.Binders.New_Function_Decl
           (Domain      => EW_Term,
            Name        => To_Ident (W => WNE_Bool_Eq),
            Return_Type => EW_Bool_Type,
            Binders     => (1 => X_Binder, 2 => Y_Binder),
            Labels      => Name_Id_Sets.Empty_Set));
      Emit
        (Theory,
         Why.Gen.Binders.New_Function_Decl
           (Domain      => EW_Term,
            Name        => New_Identifier (Name => "user_eq"),
            Return_Type => EW_Bool_Type,
            Binders     => (1 => X_Binder, 2 => Y_Binder),
            Labels      => Name_Id_Sets.Empty_Set));
   end Declare_Private_Type;

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
                   To_Name (Prefix
                            (Ada_Node => E,
                             W        => WNE_Rec_Split_Discrs,
                             M        => E_Module
                               (Unique_Entity (Root_Record_Type (E)))))));

   ---------------------------
   -- Field_Type_For_Fields --
   ---------------------------

   function Field_Type_For_Fields (E : Entity_Id) return W_Type_Id is
     (New_Type (Ada_Node   => E,
                Is_Mutable => False,
                Type_Kind  => EW_Abstract,
                Name       =>
                   To_Name (Prefix
                            (Ada_Node => E,
                             W        => WNE_Rec_Split_Fields,
                             M        => E_Module (E)))));

   ---------------------------------------
   -- Insert_Subtype_Discriminant_Check --
   ---------------------------------------

   function Insert_Subtype_Discriminant_Check
     (Ada_Node : Node_Id;
      Check_Ty : Entity_Id;
      Expr     : W_Prog_Id) return W_Prog_Id
   is
      Root : constant Entity_Id :=
        (if Fullview_Not_In_SPARK (Check_Ty) then
              Get_First_Ancestor_In_SPARK (Check_Ty)
         else Root_Record_Type (Check_Ty));
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
         elsif Fullview_Not_In_SPARK (Ty) then Get_First_Ancestor_In_SPARK (Ty)
         else Unique_Entity (Root_Record_Type (Ty)));
      Call_Id   : constant W_Identifier_Id := To_Why_Id (Field, Rec => Rec);
      Ret_Ty    : constant W_Type_Id :=
        Type_Of_Node (Search_Component_By_Name (Ty, Field));
      Top_Field : constant W_Expr_Id :=
        (if Ekind (Field) = E_Discriminant then
              New_Discriminants_Access (Ada_Node, Domain, Name, Ty)
         else New_Fields_Access (Ada_Node, Domain, Name, Ty));
   begin
      if Domain = EW_Prog and then
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
      Ty           : Entity_Id)
      return W_Expr_Id
   is
      Num_All    : constant Natural := Count_Why_Record_Fields (Ty);
      Num_Discr  : constant Natural := Number_Discriminants (Ty);
      Num_Fields : constant Natural := Count_Fields (Ty);
      Assoc      : W_Field_Association_Id;
      Assocs     : W_Field_Association_Array (1 .. Num_All);
      Index      : Natural := 0;

   begin
      if Num_Discr > 0 then
         Assoc := New_Field_Association
           (Domain   => Domain,
            Field    => Prefix (E_Module (Ty), WNE_Rec_Split_Discrs),
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
                   (Domain   => Domain,
                    Field    => Prefix (E_Module (Ty), WNE_Rec_Extension),
                    Value    => +To_Ident (WNE_Null_Extension));
            end if;

            Assoc := New_Field_Association
              (Domain   => Domain,
               Field    => Prefix (E_Module (Ty), WNE_Rec_Split_Fields),
               Value    => New_Record_Aggregate
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
           (Domain   => Domain,
            Field    => Prefix (E_Module (Ty), WNE_Attr_Tag),
            Value    => +Prefix (E_Module (Ty), WNE_Tag));
         Index := Index + 1;
         Assocs (Index) := Assoc;
      end if;

      return New_Record_Aggregate
        (Ada_Node     => Ada_Node,
         Associations => Assocs,
         Typ          => EW_Abstract (Ty));
   end New_Ada_Record_Aggregate;

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
         pragma Assert (not Is_Completely_Hidden (Anc_Comp));

         Component := Search_Component_By_Name (Ty, Anc_Comp);

         if Present (Component) then
            Assoc := New_Field_Association
              (Domain   => Domain,
               Field    => To_Why_Id (Component),
               Value    => New_Ada_Record_Access
                 (Ada_Node => Ada_Node,
                  Domain   => Domain,
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
            pragma Assert (Has_Private_Ancestor (Ty));
         end if;

         Next_Component_Or_Discriminant (Anc_Comp);
      end loop;

      if Has_Private_Ancestor (Ty) then
         declare
            Root        : constant Entity_Id :=
              Unique_Entity (Root_Record_Type (Ty));
            Anc_Is_Root : constant Boolean   := Root = Unique_Entity (Anc_Ty);
            Root_Expr : constant W_Expr_Id :=
              (if Anc_Is_Root then
                 Expr
               else
                 New_Call (Domain => EW_Term,
                           Name =>
                             Prefix (E_Module (Anc_Ty), WNE_To_Base),
                           Args => (1 => Expr)));
         begin
            Assoc := New_Field_Association
              (Domain   => Domain,
               Field    => Prefix (E_Module (Ty), WNE_Rec_Ancestor),
               Value    =>
                 New_Call (Domain => EW_Term,
                           Name =>
                             Prefix (E_Module (Ty), WNE_Hide_Ancestor),
                           Args => (1 => Root_Expr)));

            Field_Index := Field_Index + 1;
            Field_Assocs (Field_Index) := Assoc;
         end;
      end if;

      --  All discriminants of the ancestor part should have been set, but
      --  possibly not all components in case of a discriminant record.

      pragma Assert (Discr_Index = Discr_Assocs'Last);
      pragma Assert (Field_Index = Field_Assocs'Last);
   end Generate_Associations_From_Ancestor;

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
      if Domain = EW_Prog then
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
         Name     => Prefix (E_Module (Ty), WNE_Rec_Split_Discrs),
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
                 Field  => Prefix (E_Module (Ty), WNE_Rec_Split_Discrs),
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
         Name     => Prefix (E_Module (Ty), WNE_Rec_Split_Fields),
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
                 Field  => Prefix (E_Module (Ty), WNE_Rec_Split_Fields),
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
              (Ty   => Ty,
               Attr => Attribute_Constrained),
            Args     => (1 => Name),
            Domain   => Domain,
            Typ      => EW_Bool_Type);
      else
         return +True_Term;
      end if;
   end New_Is_Constrained_Access;

   -------------------------------
   -- New_Is_Constrained_Update --
   -------------------------------

   function New_Is_Constrained_Update
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Value    : W_Expr_Id;
      Ty       : Entity_Id)
      return W_Expr_Id
   is
   begin
      if Has_Defaulted_Discriminants (Ty)
        and then not Is_Constrained (Ty)
      then
         return New_Record_Update
           (Ada_Node => Ada_Node,
            Name     => Name,
            Updates  =>
              (1 =>
                   New_Field_Association
                 (Domain => Domain,
                  Field  => +New_Attribute_Expr
                    (Ty   => Ty,
                     Attr => Attribute_Constrained),
                  Value  => Value)),
            Typ      => Get_Type (Name));
      else
         return Name;
      end if;
   end New_Is_Constrained_Update;

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
           (Ty   => Ty,
            Attr => Attribute_Tag),
         Args     => (1 => Name),
         Domain   => Domain,
         Typ      => EW_Int_Type);
   end New_Tag_Access;

   ------------------------------------
   -- Prepare_Args_For_Subtype_Check --
   ------------------------------------

   function Prepare_Args_For_Subtype_Check
     (Check_Ty : Entity_Id;
      Expr     : W_Expr_Id) return W_Expr_Array
   is
      Num_Discr : constant Natural := Number_Discriminants (Check_Ty);
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

   function Record_From_Split_Form (A : W_Expr_Array; Ty  : Entity_Id)
                                    return W_Expr_Id
   is
      Associations : W_Field_Association_Array (A'Range);
      Index        : Positive := A'First;
   begin

      --  Store association for the top-level field for fields

      if Count_Fields (Ty) > 0 or else Is_Tagged_Type (Ty) then
         Associations (Index) := New_Field_Association
           (Domain   => EW_Term,
            Field    => Prefix (E_Module (Ty), WNE_Rec_Split_Fields),
            Value    => A (Index));
         Index := Index + 1;
      end if;

      --  Store association for the top-level field for discriminants

      if Number_Discriminants (Ty) > 0 then
         Associations (Index) := New_Field_Association
           (Domain   => EW_Term,
            Field    => Prefix (E_Module (Ty), WNE_Rec_Split_Discrs),
            Value    => A (Index));
         Index := Index + 1;
      end if;

      --  Store association for the 'Constrained attribute

      if not Is_Constrained (Ty) and then Has_Defaulted_Discriminants (Ty) then
         Associations (Index) := New_Field_Association
           (Domain   => EW_Term,
            Field    => +New_Attribute_Expr (Ty   => Ty,
                                             Attr => Attribute_Constrained),
            Value    => A (Index));
         Index := Index + 1;
      end if;

      --  Store association for the 'Tag attribute

      if Is_Tagged_Type (Ty) then
         Associations (Index) := New_Field_Association
           (Domain   => EW_Term,
            Field    => +New_Attribute_Expr (Ty   => Ty,
                                             Attr => Attribute_Tag),
            Value    => A (Index));
         Index := Index + 1;
      end if;

      return New_Record_Aggregate
           (Associations => Associations,
            Typ          => EW_Abstract (Ty));
   end Record_From_Split_Form;

   function Record_From_Split_Form (I : Item_Type; Ref_Allowed : Boolean)
                                    return W_Expr_Id
   is
      E      : constant Entity_Id :=
        (if I.Fields.Present then I.Fields.Binder.Ada_Node
         else I.Discrs.Binder.Ada_Node);
      Ty     : constant Entity_Id := I.Typ;
      Values : W_Expr_Array (1 .. Count_Why_Record_Fields (Ty));
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

      return Record_From_Split_Form (Values, Ty);
   end Record_From_Split_Form;

end Why.Gen.Records;
