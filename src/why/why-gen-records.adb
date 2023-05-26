------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - R E C O R D S                       --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2010-2023, AdaCore                     --
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

with Common_Containers;           use Common_Containers;
with Elists;                      use Elists;
with Flow_Utility.Initialization; use Flow_Utility.Initialization;
with GNAT.Source_Info;
with GNATCOLL.Symbols;            use GNATCOLL.Symbols;
with Gnat2Why.Expr;               use Gnat2Why.Expr;
with Namet;                       use Namet;
with Nlists;                      use Nlists;
with Sinput;                      use Sinput;
with Snames;                      use Snames;
with SPARK_Definition;
with SPARK_Definition.Annotate;   use SPARK_Definition.Annotate;
with SPARK_Util;                  use SPARK_Util;
with SPARK_Util.Hardcoded;        use SPARK_Util.Hardcoded;
with Uintp;                       use Uintp;
with VC_Kinds;                    use VC_Kinds;
with Why.Atree.Accessors;         use Why.Atree.Accessors;
with Why.Atree.Builders;          use Why.Atree.Builders;
with Why.Atree.Modules;           use Why.Atree.Modules;
with Why.Gen.Decl;                use Why.Gen.Decl;
with Why.Gen.Expr;                use Why.Gen.Expr;
with Why.Gen.Hardcoded;           use Why.Gen.Hardcoded;
with Why.Gen.Init;                use Why.Gen.Init;
with Why.Gen.Names;               use Why.Gen.Names;
with Why.Gen.Progs;               use Why.Gen.Progs;
with Why.Gen.Terms;               use Why.Gen.Terms;
with Why.Images;                  use Why.Images;
with Why.Inter;                   use Why.Inter;

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

   function Concrete_Extension_Type
     (Ty    : Entity_Id;
      Local : Boolean := True) return W_Type_Id;
   --  Return the concrete type associated to the extension type of a tagged
   --  type.

   function Count_Fields_Not_In_Root (E : Entity_Id) return Natural;
   --  Counts the number of fields for the Why3 record representing type E that
   --  are not present in the representation of the root type for E.

   procedure Create_Rep_Record_Completion_If_Needed (E : Entity_Id) with
     Pre => Is_Tagged_Type (E);
   --  Create a module for the completion of the representative type of a
   --  record if needed. It contains a concrete record type for the
   --  extension containing all components that can appear in a visible
   --  extension of the Root but do not occur in E. If E is a root type of
   --  a tagged derivation, it also contains axioms definining the
   --  extract__<comp> functions for all components of its visible extensions.
   --  Otherwise, it contains axioms giving a concrete definition to the
   --  hide__ and extract__ext__ functions of the type.

   procedure Declare_Protected_Access_Functions
     (Th           : Theory_UC;
      E            : Entity_Id;
      Root         : Entity_Id;
      Ty_Name      : W_Name_Id;
      Reuse_Discr  : Boolean;
      Init_Wrapper : Boolean);
   --  For each record field, declare an access program function, whose
   --  result is the same as the record field access, but there is a
   --  precondition (when needed).

   procedure Declare_Record_Type
     (Th           : Theory_UC;
      E            : Entity_Id;
      Root         : Entity_Id;
      Ty_Name      : W_Name_Id;
      Reuse_Discr  : Boolean;
      Init_Wrapper : Boolean);
   --  Declare the record type

   procedure Declare_Rep_Record_Type
     (Th : Theory_UC;
      E  : Entity_Id);
   --  Emit all necessary Why3 declarations to support Ada records. This also
   --  supports variant records, private types and concurrent types.
   --  @param P the Why section to insert the declaration
   --  @param E the type entity to translate

   procedure Declare_Conversion_Check_Function
     (Th   : Theory_UC;
      Root : Entity_Id);
   --  generate the program function which is used to insert subtype
   --  discriminant checks

   procedure Declare_Attributes
     (Th : Theory_UC;
      E  : Entity_Id);
   --  Declare functions for the record attributes

   procedure Declare_Component_Attributes
     (Th : Theory_UC;
      E  : Entity_Id);
   --  Declare functions for the component attributes

   procedure Declare_Conversion_Functions
     (Th           : Theory_UC;
      E            : Entity_Id;
      Root         : Entity_Id;
      Ty_Name      : W_Name_Id;
      Init_Wrapper : Boolean);
   --  Generate conversion functions from a type E to the type Root, and
   --  back.

   function Discriminant_Check_Pred_Call
     (E     : Entity_Id;
      Field : Entity_Id;
      Arg   : W_Identifier_Id)
      return W_Pred_Id;
   --  Given a record field, return a call to its discriminant check
   --  predicate, with the given argument. If that predicate is defined
   --  elsewhere (i.e. in the module for the root record type) prefix the
   --  call accordingly and add a conversion.

   function Discriminant_Check_Pred_Name
     (E            : Entity_Id;
      Field        : Entity_Id;
      Local        : Boolean;
      Relaxed_Init : Boolean := False)
      return W_Identifier_Id;
   --  Given a record field, return the name of its discrimant check
   --  predicate. If Local is true, do not prefix the identifier.
   --  If the current record type is not a root type, return the name of the
   --  corresponding predicate in the root type module.

   function Extract_Extension_Fun
     (Rec   : Entity_Id;
      Local : Boolean := True) return W_Identifier_Id;
   --  Return the name of the extract function for an extension component

   function Extract_Fun
     (Field : Entity_Id;
      Rec   : Entity_Id;
      Local : Boolean := True) return W_Identifier_Id;
   --  Return the name of the extract function for an extension

   function Get_Compatible_Tags_Module (E : Entity_Id) return W_Module_Id with
     Pre => Is_Tagged_Type (E) and then Root_Retysp (E) = E;
   --  Return the name of the module for compatibility between tags for a root
   --  tagged type E.

   function Get_Rep_Record_Completion (E : Entity_Id) return W_Module_Id;
   --  Return the name of a record's representative completion module

   function Get_Rep_Record_Module (E : Entity_Id) return W_Module_Id;
   --  Return the name of a record's representative module

   function Hidden_Ext_Name
     (Rec   : Entity_Id;
      Local : Boolean := True) return W_Identifier_Id;
   --  Record component of a concrete extension type standing for the
   --  additional unknown extensions.

   function Hidden_Component_Name
     (Field : Entity_Id;
      Rec   : Entity_Id;
      Local : Boolean := True) return W_Identifier_Id;
   --  Record component of a concrete extension type standing for a component
   --  Field not present in Rec.

   --  Module for the representation of the tag of tagged types as integers

   package Tag_Representation is

      function Get_Tag (Ty : Type_Kind_Id) return Int with
        Pre => Retysp (Ty) = Ty
        and then Is_Base_Type (Ty)
        and then Is_Tagged_Type (Ty);
      --  Return the Int value to be used for the tag of a tagged type Ty

   private

      Used_Tags     : Node_To_Int_Maps.Map;
      --  Map from tagged types to their tag value
      Last_Tag_Used : Int := 0;
      --  Last value returned for a tag

   end Tag_Representation;

   function W_Type_Of_Component
     (Field        : Entity_Id;
      Rec          : Entity_Id;
      Init_Wrapper : Boolean) return W_Type_Id
   is (if Field = Rec then
           New_Named_Type
             (Name => Get_Name (To_Local (E_Symb (Rec, WNE_Private_Type))))
       elsif Is_Type (Field) then
           New_Named_Type
             (Name => Get_Name
                (E_Symb
                     (Field, WNE_Private_Type, Relaxed_Init => Init_Wrapper)))
       else EW_Abstract
         (Etype (Field),
          Relaxed_Init => Ekind (Field) = E_Component
          and then
            (if Init_Wrapper then Has_Init_Wrapper (Etype (Field))
             else SPARK_Definition.Has_Relaxed_Init (Etype (Field)))));
   --  Compute the expected Why type of a record component. If the component is
   --  a type, it stands for the invisible fields of the type and is translated
   --  as the appropriate private type. Otherwise, return the abstract type of
   --  the component.
   --  @param Field component whose type we are interested in
   --  @param Rec record type we are currently defining if any

   ---------------------------------------
   -- Build_Binary_Predicate_For_Record --
   ---------------------------------------

   function Build_Binary_Predicate_For_Record
     (Expr1, Expr2 : W_Term_Id;
      Ty           : Entity_Id)
      return W_Pred_Id
   is
      pragma Assert (Is_Init_Wrapper_Type (Get_Type (+Expr1)) =
                     Is_Init_Wrapper_Type (Get_Type (+Expr2)));

      C_Ty    : constant Entity_Id :=
        (if Is_Class_Wide_Type (Ty) then Get_Specific_Type_From_Classwide (Ty)
         else Ty);
      Ty_Ext  : constant Entity_Id := Retysp (C_Ty);
      To_Typ  : constant W_Type_Id :=
        EW_Abstract
          (Ty_Ext,
           Relaxed_Init => Is_Init_Wrapper_Type (Get_Type (+Expr1)));
      R_Expr1 : constant W_Term_Id :=
        Insert_Simple_Conversion (Expr => Expr1,
                                  To   => To_Typ);
      R_Expr2 : constant W_Term_Id :=
        Insert_Simple_Conversion (Expr => Expr2,
                                  To   => To_Typ);
      Discrs  : constant Natural := Count_Discriminants (Ty_Ext);
      Discr   : Node_Id := (if Has_Discriminants (Ty_Ext)
                            then First_Discriminant (Ty_Ext)
                            else Empty);
      T_Comp  : W_Pred_Id;
      R_Acc1  : W_Term_Id;
      R_Acc2  : W_Term_Id;
      Tmps    : W_Identifier_Array (1 .. Discrs);
      Binds   : W_Term_Array (1 .. Discrs);
      I       : Positive := 1;
      T       : W_Pred_Id := True_Pred;

   --  Start of processing for Build_Binary_Predicate_For_Record

   begin
      --  As discriminants may occur in bounds of types of other fields,
      --  store them in the Symbol_Table.

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      while Present (Discr) loop
            R_Acc1 := New_Ada_Record_Access (Empty, R_Expr1, Discr, Ty_Ext);
            R_Acc2 := New_Ada_Record_Access (Empty, R_Expr2, Discr, Ty_Ext);

            Tmps (I) := New_Temp_Identifier
              (Discr, EW_Abstract (Etype (Discr)));
            Binds (I) := R_Acc1;

            --  We need entities of discriminants

            Insert_Tmp_Item_For_Entity (Discr, Tmps (I));

            --  Call Build_Predicate_For_Discr on discriminants

            T_Comp :=
              Build_Predicate_For_Discr
                (D_Expr1 => R_Acc1,
                 D_Expr2 => R_Acc2,
                 D_Ty    => Etype (Discr),
                 E       => Discr);

            T := New_And_Pred (T, T_Comp);

         Next_Discriminant (Discr);
         I := I + 1;
      end loop;

      --  For simple private types, we have only a single private component,
      --  the object itself.

      if Is_Simple_Private_Type (Ty_Ext) then
         if not Ignore_Private_State then
            T := Build_Predicate_For_Field
                (F_Expr1 => R_Expr1,
                 F_Expr2 => R_Expr2,
                 F_Ty    => Ty_Ext,
                 E       => Ty_Ext);
         else
            T := True_Pred;
         end if;
      else
         declare
            Fields    : Component_Sets.Set renames Get_Component_Set (Ty_Ext);
            Conjuncts : W_Pred_Array (1 .. Natural (Fields.Length));
            Count     : Natural := 0;
            T_Guard   : W_Pred_Id;
         begin
            for Field of Fields loop

               --  Only consider components visible in SPARK and Part_Of
               --  objects unless Ignore_Private_State is False.

               if not Is_Type (Field) or else not Ignore_Private_State then
                  pragma Assert (Ekind (Field) /= E_Discriminant);

                  if Is_Simple_Private_Type (Root_Retysp (Ty_Ext)) then
                     R_Acc1 := R_Expr1;
                     R_Acc2 := R_Expr2;
                  else
                     R_Acc1 := New_Ada_Record_Access
                       (Empty, R_Expr1, Field, Ty_Ext);
                     R_Acc2 := New_Ada_Record_Access
                       (Empty, R_Expr2, Field, Ty_Ext);
                  end if;

                  --  Call Build_Predicate_For_Field on fields

                  T_Comp :=
                    Build_Predicate_For_Field
                      (F_Expr1 => R_Acc1,
                       F_Expr2 => R_Acc2,
                       F_Ty    => (if Is_Type (Field) then Field
                                   else Etype (Field)),
                       E       => Field);

                  if T_Comp /= True_Pred then
                     T_Guard := New_Ada_Record_Check_For_Field
                       (Empty, R_Expr1, Field, Ty_Ext);

                     Count := Count + 1;
                     Conjuncts (Count) := New_Conditional
                       (Condition => T_Guard,
                        Then_Part => T_Comp);
                  end if;
               end if;
            end loop;

            if Count > 0 then
               T := New_And_Pred (T & Conjuncts (1 .. Count));
            end if;
         end;
      end if;

      if T /= True_Pred then
         for I in 1 .. Discrs loop
            T := New_Typed_Binding
              (Name    => Tmps (I),
               Def     => Binds (I),
               Context => T);
         end loop;
      end if;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      return T;
   end Build_Binary_Predicate_For_Record;

   --------------------------------
   -- Build_Predicate_For_Record --
   --------------------------------

   function Build_Predicate_For_Record
     (Expr : W_Term_Id; Ty : Entity_Id) return W_Pred_Id
   is
      function Build_Predicate_For_Discr
        (D_Expr1, Dummy_Expr2 : W_Term_Id; D_Ty : Entity_Id; E : Entity_Id)
         return W_Pred_Id
      is (Build_Predicate_For_Discr (D_Expr1, D_Ty, E));

      function Build_Predicate_For_Field
        (F_Expr1, Dummy_Expr2 : W_Term_Id; F_Ty : Entity_Id; E : Entity_Id)
         return W_Pred_Id
      is (Build_Predicate_For_Field (F_Expr1, F_Ty, E));

      function Build_Predicate is new Build_Binary_Predicate_For_Record
        (Build_Predicate_For_Discr,
         Build_Predicate_For_Field,
         Ignore_Private_State);

   begin
      return Build_Predicate (Expr, Expr, Ty);
   end Build_Predicate_For_Record;

   ---------------------------------
   -- Complete_Tagged_Record_Type --
   ---------------------------------

   procedure Complete_Tagged_Record_Type
     (Th : Theory_UC;
      E  : Entity_Id)
   is
   begin
      Create_Rep_Record_Completion_If_Needed (E);

      --  Export the theory containing the completion

      Add_With_Clause (Th, Get_Rep_Record_Completion (E), EW_Export);
   end Complete_Tagged_Record_Type;

   -----------------------------
   -- Concrete_Extension_Type --
   -----------------------------

   function Concrete_Extension_Type
     (Ty    : Entity_Id;
      Local : Boolean := True) return W_Type_Id
   is
      Name : constant W_Name_Id := New_Name
        (Symb   => NID (To_String (WNE_Rec_Extension_Suffix)),
         Module => (if Local then Why_Empty
                    else Get_Rep_Record_Completion (Ty)));
   begin
      return New_Named_Type (Name);
   end Concrete_Extension_Type;

   ------------------------------
   -- Count_Fields_Not_In_Root --
   ------------------------------

   function Count_Fields_Not_In_Root (E : Entity_Id) return Natural is
      Root  : constant Entity_Id := Root_Retysp (E);
      Count : Natural := 0;
   begin
      if Is_Record_Type (E) then
         for Field of Get_Component_Set (E) loop
            if No (Search_Component_In_Type (Root, Field)) then
               Count := Count + 1;
            end if;
         end loop;
      end if;

      return Count;
   end Count_Fields_Not_In_Root;

   -----------------------------------
   -- Create_Compatible_Tags_Theory --
   -----------------------------------

   procedure Create_Compatible_Tags_Theory (E : Entity_Id) is
      Compat_Tag_Symb : constant W_Identifier_Id :=
        To_Local (Get_Compatible_Tags_Predicate (E));
      Descendants     : constant Node_Sets.Set := Get_Descendant_Set (E);
      Tag1_Ident      : constant W_Identifier_Id :=
        New_Identifier (Name => "tag1", Typ => EW_Int_Type);
      Tag2_Ident      : constant W_Identifier_Id :=
        New_Identifier (Name => "tag2", Typ => EW_Int_Type);
      Tag_Binders     : constant Binder_Array :=
        (1 => (B_Name => Tag1_Ident, others => <>),
         2 => (B_Name => Tag2_Ident, others => <>));
      Th              : Theory_UC;

   begin
      Th := Open_Theory
        (WF_Context,
         Get_Compatible_Tags_Module (E),
         Comment =>
           "Module for compatibility between tags associated to type "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  Declare the renaming of __compatible_tags

      Emit
        (Th,
         New_Function_Decl
           (Domain      => EW_Pred,
            Name        => Compat_Tag_Symb,
            Binders     => Tag_Binders,
            Location    => No_Location,
            Labels      => Symbol_Sets.Empty_Set,
            Def         => New_Call
              (Domain  => EW_Pred,
               Name    => M_Compat_Tags.Compat_Tags_Id,
               Binders => Tag_Binders)));

      --  Emit axioms for the compatibility of the tags of all the descendants
      --  of E.

      declare
         procedure Generate_Axioms_For_Type (E : Type_Kind_Id);
         --  For all D in Descendants, generate an axiom giving the value of
         --  __compatible_tags <D>.tag <E>.tag, depending on whether or not
         --  D is a descendant of E.

         ------------------------------
         -- Generate_Axioms_For_Type --
         ------------------------------

         procedure Generate_Axioms_For_Type (E : Type_Kind_Id) is
            E_Descendants : constant Node_Sets.Set :=
              Get_Descendant_Set (E);
         begin
            for Descendant of Descendants loop
               if Descendant /= E then
                  declare
                     Axiom_Name : constant String :=
                       Full_Name (E)
                       & "__" & Full_Name (Descendant)
                       & "__" & Compat_Axiom;
                     Def        : W_Pred_Id := New_Call
                       (Name => Compat_Tag_Symb,
                        Args =>
                          (1 => New_Integer_Constant
                               (Value => UI_From_Int
                                    (Tag_Representation.Get_Tag
                                       (Descendant))),
                           2 => New_Integer_Constant
                             (Value => UI_From_Int
                                  (Tag_Representation.Get_Tag (E)))));

                  begin
                     if not E_Descendants.Contains (Descendant) then
                        Def := New_Not (Right => Def);
                     end if;

                     Emit
                       (Th, New_Axiom (Name => NID (Axiom_Name),
                                       Def => Def,
                                       Dep =>
                                         New_Axiom_Dep (
                                           Name => Compat_Tag_Symb,
                                           Kind => EW_Axdep_Pred)));
                  end;
               end if;
            end loop;
         end Generate_Axioms_For_Type;

      begin
         Generate_Axioms_For_Type (E);
         for Descendant of Descendants loop
            Generate_Axioms_For_Type (Descendant);
         end loop;
      end;

      Close_Theory (Th, Kind => Definition_Theory);
   end Create_Compatible_Tags_Theory;

   --------------------------------------------
   -- Create_Rep_Record_Completion_If_Needed --
   --------------------------------------------

   procedure Create_Rep_Record_Completion_If_Needed (E : Entity_Id) is

      procedure Complete_Extraction_Functions with
        Pre => E /= Root_Retysp (E);
      --  Emit axioms definining the extract__<comp> functions for all
      --  components of E.

      procedure Complete_Hide_Function with
        Pre => E /= Root_Retysp (E);
      --  Emit axioms giving a concrete definition to the hide__ and
      --  extract__ext__ functions of the type E.

      procedure Declare_Extension_Type;
      --  Declare a concrete record type for the extension part of E. It
      --  contains all components that can appear in a visible extension of the
      --  root type of E but do not occur in E.

      Root       : constant Entity_Id := Root_Retysp (E);
      Ancestor   : constant Entity_Id :=
        Oldest_Parent_With_Same_Fields (E);
      E_Ext_Type : constant W_Type_Id := New_Named_Type
        (Name => Get_Name (E_Symb (E, WNE_Extension_Type)));
      Th         : Theory_UC;

      -----------------------------------
      -- Complete_Extraction_Functions --
      -----------------------------------

      procedure Complete_Extraction_Functions is
         Concrete_Root_Type : constant W_Type_Id :=
           Concrete_Extension_Type (Root);
         Root_Ext_Id        : constant W_Identifier_Id :=
           To_Local (E_Symb (Root, WNE_Rec_Extension));

      begin
         for Field of Get_Component_Set (E) loop
            if Original_Declaration (Field) = E then

               --  Generate:
               --  axiom extract__<comp>__def:
               --   forall ext : __ext_type.
               --     extract__<comp> ext = (root_ext.open ext).<comp>

               declare
                  Field_Id     : constant W_Identifier_Id :=
                    Hidden_Component_Name (Field, Root, Local => False);
                  Id           : constant W_Identifier_Id :=
                    Extract_Fun (Field, Rec => E, Local => False);
                  Extract_Call : W_Expr_Id := New_Call
                    (Domain => EW_Term,
                     Name   => Id,
                     Args   => (1 => +Root_Ext_Id),
                     Typ    => W_Type_Of_Component
                       (Field, E, Init_Wrapper => False));
                  --  extract__<comp> ext

               begin

                  --  If field is a true component, then we might need a
                  --  conversion so that it has the type of the root component.

                  if not Is_Type (Field) then
                     Extract_Call := Insert_Simple_Conversion
                       (Domain         => EW_Term,
                        Expr           => Extract_Call,
                        To             => Get_Typ (Field_Id),
                        Force_No_Slide => True);
                  end if;

                  Emit (Th,
                        New_Guarded_Axiom
                          (Name     =>
                             NID (Img (Get_Symb
                               (Get_Name (Extract_Fun (Field, Rec => E))))
                               & "__def"),
                           Binders  => (1 => (B_Name => Root_Ext_Id,
                                              others => <>)),
                           Def      => +New_Comparison
                             (Symbol => Why_Eq,
                              Left   => Extract_Call,
                              Right  => New_Record_Access
                                (Name  => New_Call
                                     (Domain  => EW_Term,
                                      Name    => New_Identifier
                                        (Name   => To_String (WNE_Open),
                                         Module =>
                                           Get_Rep_Record_Completion (Root)),
                                      Args    => (1 => +Root_Ext_Id),
                                      Typ     => Concrete_Root_Type),
                                 Field => Field_Id,
                                 Typ   => Get_Typ (Field_Id)),
                              Domain => EW_Term),
                           Dep      =>
                             New_Axiom_Dep
                               (Name => Id,
                                Kind => EW_Axdep_Func)));
               end;
            end if;
         end loop;
      end Complete_Extraction_Functions;

      ----------------------------
      -- Complete_Hide_Function --
      ----------------------------

      procedure Complete_Hide_Function is
         Ext_Comps       : constant Node_Sets.Set :=
           Get_Extension_Components (Root);

         Root_Ext_Type      : constant W_Type_Id := New_Named_Type
           (Name => Get_Name (E_Symb (Root, WNE_Extension_Type)));
         --  Abstract extension type of the root
         Concrete_Root_Type : constant W_Type_Id := Concrete_Extension_Type
           (Root, Local => False);
         --  Concrete extension type of the root
         Concrete_E_Type    : constant W_Type_Id :=
           Concrete_Extension_Type (E);
         --  Concrete extension type of E
         E_Open_Ext_Id      : constant W_Identifier_Id := New_Temp_Identifier
           (Base_Name => "open_ext",
            Typ       => Concrete_E_Type);
         R_Open_Ext_Id      : constant W_Identifier_Id := New_Temp_Identifier
           (Base_Name => "open_ext",
            Typ       => Concrete_Root_Type);
         --  Temporary identifiers for the concrete view of Root and E
         --  extensions.
         Number_Of_Exts     : constant Natural :=
           Natural (Ext_Comps.Length)
           + 1;  --  for the extension field of the current type
         Hide_Binders       : Binder_Array (1 .. Number_Of_Exts);
         R_Associations     : W_Field_Association_Array (1 .. Number_Of_Exts);
         E_Associations     : W_Field_Association_Array (1 .. Number_Of_Exts);
         Num_Binders        : Natural := 0;
         Num_R_Assocs       : Natural := 0;
         Num_E_Assocs       : Natural := 0;

      begin
         --  Store in Hide_Binders a binder for each component of Ext_Comps
         --  which is present in E:
         --    Hide_Binders := (tmp_comp1 : t1, ...)
         --  Store in R_Associations the associations for the definition of
         --  hide__ext__, see below. If the component is present in E, use
         --  a binder from Hide_Binders, otherwise, look for it in
         --  E_Open_Ext_Id:
         --    R_Associations :=
         --      (comp1 => tmp_comp1, ...,
         --       hidden_comp1 => e_open_ext.hidden_comp1, ...)
         --  Store in E_Associations the associations for the definition of
         --  extract__ext__, see below. Each component of Ext_Comps which is
         --  not present in E is associated to the corresponding component
         --  in R_Open_Ext_Id:
         --    E_Associations :=
         --      (hidden_comp1 => r_open_ext.hidden_comp1, ...)

         for Field of Ext_Comps loop
            declare
               E_Field    : constant Entity_Id :=
                 Search_Component_In_Type (E, Field);
               E_Field_Id : W_Identifier_Id;
               R_Field_Id : constant W_Identifier_Id :=
                 Hidden_Component_Name (Field, Root, Local => False);
            begin
               if Present (E_Field) then
                  Num_Binders := Num_Binders + 1;
                  E_Field_Id := New_Temp_Identifier
                    (Base_Name => Short_Name (E_Field),
                     Typ       => W_Type_Of_Component
                       (E_Field, Root, Init_Wrapper => False));
                  Hide_Binders (Num_Binders) :=
                    (B_Name => E_Field_Id,
                     others => <>);

                  Num_R_Assocs := Num_R_Assocs + 1;
                  R_Associations (Num_R_Assocs) := New_Field_Association
                    (Domain => EW_Term,
                     Field  => R_Field_Id,
                     Value  =>
                       (if Is_Type (Field) then +E_Field_Id
                        else Insert_Simple_Conversion
                          (Domain         => EW_Term,
                           Expr           => +E_Field_Id,
                           To             => Get_Typ (R_Field_Id),
                           Force_No_Slide => True)));
               else
                  E_Field_Id := Hidden_Component_Name (Field, E);
                  Num_R_Assocs := Num_R_Assocs + 1;
                  R_Associations (Num_R_Assocs) := New_Field_Association
                    (Domain => EW_Term,
                     Field  => R_Field_Id,
                     Value  => New_Record_Access
                       (Name  => +E_Open_Ext_Id,
                        Field => E_Field_Id,
                        Typ   => Get_Typ (R_Field_Id)));
                  Num_E_Assocs := Num_E_Assocs + 1;
                  E_Associations (Num_E_Assocs) := New_Field_Association
                    (Domain => EW_Term,
                     Field  => E_Field_Id,
                     Value  => New_Record_Access
                       (Name  => +R_Open_Ext_Id,
                        Field => R_Field_Id,
                        Typ   => Get_Typ (R_Field_Id)));
               end if;
            end;
         end loop;

         --  Add the extension field to Hide_Binders

         declare
            E_Ext_Id : constant W_Identifier_Id :=
              New_Temp_Identifier (Base_Name => "ext", Typ => E_Ext_Type);
         begin
            Num_Binders := Num_Binders + 1;
            Hide_Binders (Num_Binders) :=
              (B_Name => E_Ext_Id,
               others => <>);
         end;

         --  Add the hidden extension field to R_Associations
         --  and E_Associations.

         Num_R_Assocs := Num_R_Assocs + 1;
         R_Associations (Num_R_Assocs) := New_Field_Association
           (Domain => EW_Term,
            Field  => Hidden_Ext_Name (Root, Local => False),
            Value  => New_Record_Access
              (Name  => +E_Open_Ext_Id,
               Field => Hidden_Ext_Name (E),
               Typ   => EW_Private_Type));

         Num_E_Assocs := Num_E_Assocs + 1;
         E_Associations (Num_E_Assocs) := New_Field_Association
           (Domain => EW_Term,
            Field  => Hidden_Ext_Name (E),
            Value  => New_Record_Access
              (Name  => +R_Open_Ext_Id,
               Field => Hidden_Ext_Name (Root, Local => False),
               Typ   => EW_Private_Type));

         --  axiom hide__ext__def:
         --   forall tmp_comp1 : t1 ..  ext : __exp_type.
         --     let open_ext = open ext in
         --     Root.open (hide__ext__ (tmp_comp1, .. , ext))
         --      = { comp1        => tmp_comp1, ..,
         --          hidden_comp1 => open_ext.hidden_comp1, ..,
         --          hidden_ext   => open_ext.hidden_ext }

         declare
            Hide_Name : constant W_Identifier_Id :=
              New_Identifier
                (Name   => To_String (WNE_Hide_Extension),
                 Module => Get_Rep_Record_Module (E),
                 Typ    => Root_Ext_Type);
            Comp      : constant W_Pred_Id :=
              +New_Comparison
              (Symbol => Why_Eq,
               Left   => New_Call
                 (Domain => EW_Term,
                  Name   => New_Identifier
                    (Name   => To_String (WNE_Open),
                     Module => Get_Rep_Record_Completion (Root)),
                  Args   => (1 => New_Call
                             (Domain  => EW_Term,
                              Name    => Hide_Name,
                              Binders => Hide_Binders
                                (1 .. Num_Binders),
                              Typ     => Root_Ext_Type)),
                  Typ    => Concrete_Root_Type),
               Right  => New_Record_Aggregate
                 (Associations => R_Associations),
               Domain => EW_Pred);
            Id        : constant W_Identifier_Id :=
              New_Identifier (Name => To_String (WNE_Open));
            Def       : constant W_Pred_Id :=
              New_Binding
                (Name     => E_Open_Ext_Id,
                 Def      => New_Call
                   (Name   => Id,
                    Args   =>
                      (1 => +Hide_Binders (Num_Binders).B_Name),
                    Typ    => Get_Typ (E_Open_Ext_Id)),
                 Context  => Comp);
         begin
            Emit (Th,
                  New_Guarded_Axiom
                    (Name     =>
                       NID (To_String (WNE_Hide_Extension) & "def"),
                     Binders  => Hide_Binders (1 .. Num_Binders),
                     Def      => Def,
                     Dep      => New_Axiom_Dep (Name => Id,
                                                Kind => EW_Axdep_Func)));
         end;

         --  For the extension field, generate:
         --  axiom extract___ext____def:
         --   forall ext : Root.__exp_type.
         --     let open_ext = Root.open ext in
         --     open (extract__ext__ ext) =
         --       { hidden_comp1 => open_ext.hidden_comp1, ..,
         --         hidden_ext   => open_ext.hidden_ext }

         declare
            Extract_Func : constant W_Identifier_Id := Extract_Extension_Fun
              (E, Local => False);
            Root_Ext_Id  : constant W_Identifier_Id :=
              New_Temp_Identifier (Base_Name => "ext", Typ => Root_Ext_Type);
         begin

            Emit (Th,
                  New_Guarded_Axiom
                    (Name    =>
                       NID (To_String (WNE_Extract_Prefix) &
                           To_String (WNE_Rec_Extension_Suffix) & "def"),
                     Binders => (1 => (B_Name => Root_Ext_Id,
                                        others => <>)),
                     Def     => New_Binding
                       (Name     => R_Open_Ext_Id,
                        Def      => New_Call
                          (Name   => New_Identifier
                             (Name   => To_String (WNE_Open),
                              Module => Get_Rep_Record_Completion (Root)),
                           Args   => (1 => +Root_Ext_Id),
                           Typ    => Get_Typ (R_Open_Ext_Id)),
                        Context  => +New_Comparison
                          (Symbol => Why_Eq,
                           Left   => New_Call
                             (Domain => EW_Term,
                              Name   => New_Identifier
                                (Name => To_String (WNE_Open)),
                              Args   => (1 => New_Call
                                           (Domain => EW_Term,
                                            Name   => Extract_Func,
                                            Args   => (1 => +Root_Ext_Id),
                                            Typ    => E_Ext_Type)),
                              Typ    => Concrete_E_Type),
                           Right  => New_Record_Aggregate
                             (Associations =>
                                  E_Associations (1 .. Num_E_Assocs)),
                           Domain => EW_Pred))));
         end;
      end Complete_Hide_Function;

      ----------------------------
      -- Declare_Extension_Type --
      ----------------------------

      procedure Declare_Extension_Type is
         Ext_Comps : constant Node_Sets.Set := Get_Extension_Components (Root);
         Binders   : Binder_Array (1 .. Natural (Ext_Comps.Length) + 1);
         Index     : Natural := 0;

      begin
         --  Add a field for each extension of Root not visible in E

         for Field of Ext_Comps loop
            if E = Root or else No (Search_Component_In_Type (E, Field)) then
               Index := Index + 1;
               Binders (Index) :=
                 (B_Name   => Hidden_Component_Name (Field, E),
                  Ada_Node => Field,
                  others   => <>);
            end if;
         end loop;

         --  Add a field of type __private representing the unknown extension
         --  components.

         Index := Index + 1;
         Binders (Index) :=
           (B_Name => New_Identifier
              (Domain => EW_Term,
               Name   => To_String (WNE_Hidden_Extension),
               Module => Why_Empty,
               Typ    => EW_Private_Type),
            others => <>);

         Emit_Record_Declaration
           (Th           => Th,
            Name         => Get_Name (Concrete_Extension_Type (E)),
            Binders      => Binders (1 .. Index),
            SPARK_Record => False);
      end Declare_Extension_Type;

   --  Start of processing for Create_Rep_Record_Completion_If_Needed

   begin
      --  Empty record types and clones do not require a representative
      --  theory.

      if Count_Why_Top_Level_Fields (E) = 0
        or else Record_Type_Is_Clone (E)
      then
         return;
      end if;

      --  If E has an ancestor with the same fields, use its representative

      if Ancestor /= E then
         return;
      end if;

      Th := Open_Theory
        (WF_Context,
         Get_Rep_Record_Completion (E),
         Comment =>
           "Module for completing the tagged record theory associated to type "
         & """" & Get_Name_String (Chars (E)) & """"
         & (if Sloc (E) > 0 then
              " defined at " & Build_Location_String (Sloc (E))
           else "")
         & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      --  Declare a concrete record type for the extensions of E

      Declare_Extension_Type;

      --  Link it to the abstract extension type using Open and Close

      Emit (Th,
            New_Clone_Declaration
              (Theory_Kind   => EW_Module,
               Clone_Kind    => EW_Export,
               As_Name       => No_Symbol,
               Origin        => Incomp_Ty_Conv,
               Substitutions =>
                 (1 => New_Clone_Substitution
                      (Kind      => EW_Type_Subst,
                       Orig_Name => New_Name
                         (Symb => NID ("abstr_ty")),
                       Image     => Get_Name (E_Ext_Type)),
                  2 => New_Clone_Substitution
                    (Kind      => EW_Type_Subst,
                     Orig_Name => New_Name
                       (Symb => NID ("comp_ty")),
                     Image     => Get_Name (Concrete_Extension_Type (E))))));

      --  Add defining axioms for the abstract functions for extraction and
      --  collapse of the type extension.

      if E /= Root then
         Complete_Extraction_Functions;
         Complete_Hide_Function;
      end if;

      Close_Theory (Th, Kind => Axiom_Theory, Defined_Entity => E);
   end Create_Rep_Record_Completion_If_Needed;

   ----------------------------------------
   -- Create_Rep_Record_Theory_If_Needed --
   ----------------------------------------

   procedure Create_Rep_Record_Theory_If_Needed (E : Entity_Id)
   is
      Ancestor : constant Entity_Id := Oldest_Parent_With_Same_Fields (E);
      Th       : Theory_UC;
   begin
      --  Empty record types and clones do not require a representative
      --  theory.

      if Count_Why_Top_Level_Fields (E) = 0
        or else Record_Type_Is_Clone (E)
      then
         return;
      end if;

      --  If E has an ancestor with the same fields, use its representative

      if Ancestor /= E then
         return;
      end if;

      Th :=
        Open_Theory
          (WF_Context, Get_Rep_Record_Module (E),
           Comment =>
             "Module for axiomatizing the record theory associated to type "
           & """" & Get_Name_String (Chars (E)) & """"
           & (if Sloc (E) > 0 then
                " defined at " & Build_Location_String (Sloc (E))
             else "")
           & ", created in " & GNAT.Source_Info.Enclosing_Entity);

      Declare_Rep_Record_Type (Th, E);

      Close_Theory (Th, Kind => Definition_Theory, Defined_Entity => E);
   end Create_Rep_Record_Theory_If_Needed;

   ------------------------
   -- Declare_Ada_Record --
   ------------------------

   procedure Declare_Ada_Record
     (Th : Theory_UC;
      E  : Entity_Id)
   is
      Root     : constant Entity_Id := Root_Retysp (E);
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
            Emit (Th,
                  New_Type_Decl
                    (Name   => Ty_Name,
                     Labels => Symbol_Sets.Empty_Set));
         else
            Emit (Th,
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
              (Th,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (E_Symb (E, WNE_To_Base)),
                  Binders     => R_Binder,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Return_Type => (if Is_Root then Abstr_Ty
                                  else EW_Abstract (Root)),
                  Def         => +A_Ident));
            Emit
              (Th,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (E_Symb (E, WNE_Of_Base)),
                  Binders     => Binder_Array'(1 => (B_Name => R_Ident,
                                                     others => <>)),
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Return_Type => Abstr_Ty,
                  Def         => +R_Ident));
         end;

         --  Equality function returns always true

         declare
            B_Ident : constant W_Identifier_Id :=
              New_Identifier (Name => "b", Typ => Abstr_Ty);
         begin

            Emit
              (Th,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (E_Symb (E, WNE_Bool_Eq)),
                  Binders     =>
                    R_Binder &
                    Binder_Array'(1 => Binder_Type'(B_Name => B_Ident,
                                                    others => <>)),
                  Return_Type => +EW_Bool_Type,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Def         => +True_Term));
         end;

         Declare_Attributes (Th, E);

         return;
      end if;

      if Record_Type_Is_Clone (E) then

         --  This type is simply a copy of an existing type, we re-export the
         --  corresponding module and then return.

         declare
            Clone : constant Entity_Id := Record_Type_Cloned_Subtype (E);
         begin
            Add_With_Clause (Th, E_Module (Clone), EW_Export);

            --  If the copy has the same name as the original, do not redefine
            --  the type name.

            if Short_Name (E) /= Short_Name (Clone) then
               Emit (Th,
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

      Add_With_Clause (Th, Rep_Module, EW_Export);

      --  Rename the representative record type as expected.

      Emit (Th,
            New_Type_Decl
              (Name  => To_Why_Type (E, Local => True),
               Alias =>
                 +New_Named_Type
                   (Name => To_Name (WNE_Rec_Rep))));

      --  The static tag for the type is defined as a logic constant. For new
      --  types, we use a fresh integer value so all tags can be proved to be
      --  different. For subtypes, we reuse the tag of the base type.

      if Is_Tagged_Type (E) then
         Emit (Th,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (E_Symb (E, WNE_Tag)),
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => EW_Int_Type,
                  Def         => New_Integer_Constant
                    (Value => UI_From_Int
                         (Tag_Representation.Get_Tag (Base_Retysp (E))))));
      end if;

      if Root = E
        and then Has_Discriminants (E)
        and then not Is_Constrained (E)
      then
         Declare_Conversion_Check_Function (Th, Root);
      end if;

      Declare_Attributes (Th, E);
      Declare_Component_Attributes (Th, E);
   end Declare_Ada_Record;

   ------------------------
   -- Declare_Attributes --
   ------------------------

   procedure Declare_Attributes
     (Th : Theory_UC;
      E  : Entity_Id)
   is
   begin
      --  The value size is defined as a logic constant

      Emit (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_Attr_Value_Size)),
               Labels      => Symbol_Sets.Empty_Set,
               Location    => No_Location,
               Return_Type => EW_Int_Type));

      --  The object size is defined as a logic constant

      Emit (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_Attr_Object_Size)),
               Labels      => Symbol_Sets.Empty_Set,
               Location    => No_Location,
               Return_Type => EW_Int_Type));

      --  The alignement is defined as a logic constant

      Emit (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_Attr_Alignment)),
               Labels      => Symbol_Sets.Empty_Set,
               Location    => No_Location,
               Return_Type => EW_Int_Type));

      declare
         Zero : constant W_Expr_Id :=
           New_Integer_Constant (Value => Uint_0);

         --  Value size is non-negative

         Value_Size_Fun : constant W_Expr_Id :=
           New_Call (Name   => To_Local (E_Symb (E, WNE_Attr_Value_Size)),
                     Domain => EW_Term,
                     Typ    => EW_Int_Type);

         Value_Size_Axiom : constant W_Pred_Id :=
           +New_Comparison (Symbol => Int_Infix_Ge,
                            Left   => Value_Size_Fun,
                            Right  => Zero,
                            Domain => EW_Term);

         --  Object size is non-negative

         Object_Size_Fun : constant W_Expr_Id :=
           New_Call (Name   => To_Local (E_Symb (E, WNE_Attr_Object_Size)),
                     Domain => EW_Term,
                     Typ    => EW_Int_Type);

         Object_Size_Axiom : constant W_Pred_Id :=
           +New_Comparison (Symbol => Int_Infix_Ge,
                            Left   => Object_Size_Fun,
                            Right  => Zero,
                            Domain => EW_Term);

         --  Alignment is non-negative

         Alignment_Fun : constant W_Expr_Id :=
           New_Call (Name     => To_Local (E_Symb (E, WNE_Attr_Alignment)),
                     Domain   => EW_Term,
                     Typ      => EW_Int_Type);

         Alignment_Axiom : constant W_Pred_Id :=
           +New_Comparison (Symbol => Int_Infix_Ge,
                            Left   => Alignment_Fun,
                            Right  => Zero,
                            Domain => EW_Term);
      begin
         Emit (Th,
               New_Axiom (Ada_Node => E,
                          Name     => NID ("value__size_axiom"),
                          Def      => Value_Size_Axiom,
                          Dep      =>
                            New_Axiom_Dep (
                              Name =>
                                To_Local (E_Symb (E, WNE_Attr_Value_Size)),
                              Kind => EW_Axdep_Func)));

         Emit (Th,
               New_Axiom (Ada_Node => E,
                          Name     => NID ("object__size_axiom"),
                          Def      => Object_Size_Axiom,
                          Dep      =>
                            New_Axiom_Dep (
                              Name =>
                                To_Local (E_Symb (E, WNE_Attr_Object_Size)),
                              Kind => EW_Axdep_Func)));

         Emit (Th,
               New_Axiom (Ada_Node => E,
                          Name     => NID ("alignment_axiom"),
                          Def      => Alignment_Axiom,
                          Dep      =>
                            New_Axiom_Dep (
                              Name =>
                                To_Local (E_Symb (E, WNE_Attr_Alignment)),
                              Kind => EW_Axdep_Func)));

      end;
   end Declare_Attributes;

   ----------------------------------
   -- Declare_Component_Attributes --
   ----------------------------------

   procedure Declare_Component_Attributes
     (Th : Theory_UC;
      E  : Entity_Id)
   is
      procedure Declare_Attribute_For_Field (Field : Entity_Id);
      --  Declare attributes for Field only.
      --  @param Field component of discriminant of E

      ---------------------------------
      -- Declare_Attribute_For_Field --
      ---------------------------------

      procedure Declare_Attribute_For_Field (Field : Entity_Id) is
         Axiom : constant String :=
           Full_Name (Representative_Component (Field));

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
         Emit (Th,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        =>
                    To_Local (E_Symb (Field, WNE_Attr_First_Bit)),
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => EW_Int_Type));

         Emit (Th,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        =>
                    To_Local (E_Symb (Field, WNE_Attr_Last_Bit)),
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => EW_Int_Type));

         Emit (Th,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        =>
                    To_Local (E_Symb (Field, WNE_Attr_Position)),
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => EW_Int_Type));

         Emit (Th,
               New_Axiom (Ada_Node => Field,
                          Name     => NID (Axiom & "__first__bit_axiom"),
                          Def      => First_Bit_Axiom,
                          Dep      => New_Axiom_Dep (
                            Name =>
                              To_Local (E_Symb (Field, WNE_Attr_First_Bit)),
                            Kind => EW_Axdep_Func)));

         Emit (Th,
               New_Axiom (Ada_Node => Field,
                          Name     => NID (Axiom & "__last__bit_axiom"),
                          Def      => Last_Bit_Axiom,
                          Dep      => New_Axiom_Dep (
                            Name =>
                              To_Local (E_Symb (Field, WNE_Attr_Last_Bit)),
                            Kind => EW_Axdep_Func)));

         Emit (Th,
               New_Axiom (Ada_Node => Field,
                          Name     => NID (Axiom & "__position_axiom"),
                          Def      => Position_Axiom,
                          Dep      => New_Axiom_Dep (
                            Name =>
                              To_Local (E_Symb (Field, WNE_Attr_Position)),
                            Kind => EW_Axdep_Func)));
      end Declare_Attribute_For_Field;

   --  Start of processing for Declare_Component_Attributes

   begin
      if Has_Discriminants (E) then
         declare
            Discr : Entity_Id := First_Discriminant (E);
         begin
            while Present (Discr) loop
               Declare_Attribute_For_Field (Discr);
               Next_Discriminant (Discr);
            end loop;
         end;
      end if;

      for Field of Get_Component_Set (E) loop
         if Ekind (Field) = E_Component then
            Declare_Attribute_For_Field (Field);
         end if;
      end loop;
   end Declare_Component_Attributes;

   ---------------------------------------
   -- Declare_Conversion_Check_Function --
   ---------------------------------------

   procedure Declare_Conversion_Check_Function
     (Th   : Theory_UC;
      Root : Entity_Id)
   is
      Fields_Name : constant W_Name_Id := To_Local
        (Get_Name (E_Symb (Root, WNE_Rec_Split_Discrs)));
      Root_Fields : constant W_Type_Id :=
        +New_Named_Type (Name => Fields_Name);
      A_Ident    : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Root_Fields);
      Num_Discr  : constant Natural := Count_Discriminants (Root);
      Discr      : Node_Id;
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
      Discr := First_Discriminant (Root);

      loop
         Args (Count) := +To_Why_Id
           (Discr, Local => True, Rec   => Root,
            Typ          => Base_Why_Type (Etype (Discr)));
         R_Binder (Count) :=
           Binder_Type'
             (B_Name => +Args (Count),
              others => <>);
         Check_Pred :=
           +New_And_Expr
           (Domain => EW_Pred,
            Left   => +Check_Pred,
            Right  =>
              New_Call
                (Domain => EW_Pred,
                 Name   => Why_Eq,
                 Typ    => EW_Bool_Type,
                 Args   =>
                   (1 => +Args (Count),
                    2 =>
                      Insert_Simple_Conversion
                        (Domain   => EW_Term,
                         Expr     => New_Record_Access
                           (Ada_Node => Root,
                            Name     => +A_Ident,
                            Field    => To_Why_Id
                              (Discr, Local => True, Rec => Root),
                            Typ      => EW_Abstract (Etype (Discr))),
                         To       =>
                           Base_Why_Type (Etype (Discr))))));
         Count := Count + 1;
         Next_Discriminant (Discr);
         exit when No (Discr);
      end loop;

      Emit (Th,
            New_Function_Decl
              (Domain   => EW_Pred,
               Name     => To_Local (E_Symb (Root, WNE_Range_Pred)),
               Location => No_Location,
               Labels   => Symbol_Sets.Empty_Set,
               Binders  => R_Binder,
               Def      => +Check_Pred));
      Pre_Cond :=
        New_Call (Name => To_Local (E_Symb (Root, WNE_Range_Pred)),
                  Args => Args);
      Emit (Th,
            New_Function_Decl
              (Domain      => EW_Prog,
               Name        => To_Local (E_Symb (Root, WNE_Range_Check_Fun)),
               Binders     => R_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => EW_Unit_Type,
               Pre         => Pre_Cond));
   end Declare_Conversion_Check_Function;

   ----------------------------------
   -- Declare_Conversion_Functions --
   ----------------------------------

   procedure Declare_Conversion_Functions
     (Th           : Theory_UC;
      E            : Entity_Id;
      Root         : Entity_Id;
      Ty_Name      : W_Name_Id;
      Init_Wrapper : Boolean)
   is
      Num_Discrs      : constant Natural := Count_Discriminants (E);
      Num_E_Fields    : constant Natural := Count_Why_Regular_Fields (E);
      Num_Root_Fields : constant Natural := Count_Why_Regular_Fields (Root);
      Num_E_All       : constant Natural := Count_Why_Top_Level_Fields (E);
      Num_Root_All    : constant Natural :=
        Count_Why_Top_Level_Fields (Root);
      To_Root_Aggr    : W_Field_Association_Array (1 .. Num_Root_All);
      From_Root_Aggr  : W_Field_Association_Array (1 .. Num_E_All);
      From_Index      : Natural := 0;
      To_Index        : Natural := 0;

      Abstr_Ty  : constant W_Type_Id     := New_Named_Type (Name => Ty_Name);
      A_Ident   : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Abstr_Ty);
      R_Binder  : constant Binder_Array :=
        (1 => (B_Name => A_Ident,
               others => <>));
      R_Ident         : constant W_Identifier_Id :=
        New_Identifier
          (Name => "r",
           Typ  => EW_Abstract (Root, Relaxed_Init => Init_Wrapper));
      From_Binder     : constant Binder_Array :=
        (1 => (B_Name => R_Ident,
               others => <>));
   begin
      pragma Assert (Is_Tagged_Type (E) or else Num_E_All <= Num_Root_All);

      --  The current type may have components that are not present in the
      --  root type, corresponding to extensions of a tagged type. The root
      --  type should not have components that are not present in the
      --  current type.

      --  When converting between the root type and the current type,
      --  components that are present in both types are simply copied
      --  (possibly with a conversion). Components from the target type
      --  that are not present in the source type are synthesized:

      --  . for an extension component <comp> when converting to the current
      --    type, call extract__<comp> on the extension field in the source
      --    value.

      --  . for the extension component rec__ext__ when converting to the
      --    root type, call hide_extension on all the extension fields in
      --    the source value.

      --  Step 1. Convert the __split_discrs field for discriminants

      --  Copy all discriminants between the root type and the current type,
      --  which should have exactly the same discriminants in SPARK.

      if Num_Discrs > 0 then
         declare
            Orig_D_Id      : constant W_Identifier_Id :=
              E_Symb (Root, WNE_Rec_Split_Discrs, Init_Wrapper);
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
              E_Symb (Root, WNE_Rec_Split_Fields, Init_Wrapper);
            E_Field_Access  : constant W_Expr_Id :=
              New_Record_Access (Name  => +A_Ident,
                                 Field => To_Ident (WNE_Rec_Split_Fields));
            R_Field_Access  : constant W_Expr_Id :=
              New_Record_Access (Name  => +R_Ident,
                                 Field => Orig_F_Id);

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

            for Field of Get_Component_Set (E) loop
               declare
                  Orig     : constant Entity_Id :=
                    Search_Component_In_Type (Root, Field);
                  Orig_Id  : W_Identifier_Id;
                  Field_Id : constant W_Identifier_Id :=
                    To_Why_Id (Field, Local => True, Rec => E);

               begin
                  if Present (Orig) then

                     --  If we are generating functions for the init wrapper
                     --  module, get fields from the correct place

                     Orig_Id := To_Why_Id
                       (Orig, Rec => Root, Relaxed_Init => Init_Wrapper);

                     Field_From_Index := Field_From_Index + 1;
                     From_Root_Field (Field_From_Index) :=
                       New_Field_Association
                         (Domain => EW_Term,
                          Field  => Field_Id,
                          Value  =>
                            Insert_Simple_Conversion
                              (Domain         => EW_Term,
                               To             => W_Type_Of_Component
                                 (Field, E, Init_Wrapper),
                               Expr           =>
                                 New_Record_Access
                                   (Name  => R_Field_Access,
                                    Field => Orig_Id,
                                    Typ   => W_Type_Of_Component
                                      (Orig, E, Init_Wrapper)),
                               Force_No_Slide => True));

                     Field_To_Index := Field_To_Index + 1;
                     To_Root_Field (Field_To_Index) :=
                       New_Field_Association
                         (Domain => EW_Term,
                          Field  => Orig_Id,
                          Value  =>
                            Insert_Simple_Conversion
                              (Domain         => EW_Term,
                               To             => W_Type_Of_Component
                                 (Orig, E, Init_Wrapper),
                               Expr           =>
                                 New_Record_Access
                                   (Name  => E_Field_Access,
                                    Field => Field_Id,
                                    Typ   =>
                                      W_Type_Of_Component
                                        (Field, E, Init_Wrapper)),
                               Force_No_Slide => True));
                  else
                     pragma Assert (Is_Tagged_Type (E));
                     Field_From_Index := Field_From_Index + 1;
                     From_Root_Field (Field_From_Index) :=
                       New_Field_Association
                         (Domain => EW_Term,
                          Field  => Field_Id,
                          Value  =>
                            +W_Term_Id'(New_Call
                            (Name =>
                               Extract_Fun (Field, Rec => E),
                             Args =>
                               (1 => New_Record_Access
                                  (Name  => R_Field_Access,
                                   Field =>
                                     +E_Symb (Root, WNE_Rec_Extension),
                                   Typ   => EW_Private_Type)))));
                  end if;
               end;
            end loop;

            --  Step 2.2. Deal with extension field for tagged types

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
                      (Name => Extract_Extension_Fun (E),
                       Args =>
                         (1 => New_Record_Access
                            (Name  => R_Field_Access,
                             Field => +E_Symb (Root, WNE_Rec_Extension),
                             Typ   => EW_Private_Type)))));

               declare
                  Num_Args : constant Natural :=
                    Count_Fields_Not_In_Root (E)
                    + 1;  --  for the extension field of the current type;
                  Args     : W_Expr_Array (1 .. Num_Args);
                  Index    : Natural := 0;
               begin
                  for Field of Get_Component_Set (E) loop
                     if No (Search_Component_In_Type (Root, Field)) then
                        Index := Index + 1;
                        Args (Index) :=
                          New_Record_Access
                            (Name  => E_Field_Access,
                             Field =>
                               To_Why_Id (Field, Local => True, Rec => E),
                             Typ   => W_Type_Of_Component
                               (Field, E, Init_Wrapper));
                     end if;
                  end loop;

                  Index := Index + 1;
                  Args (Index) :=
                    New_Record_Access
                      (Name  => E_Field_Access,
                       Field => To_Local (E_Symb (E, WNE_Rec_Extension)),
                       Typ   => EW_Private_Type);

                  pragma Assert (Index = Num_Args);

                  Field_To_Index := Field_To_Index + 1;
                  To_Root_Field (Field_To_Index) :=
                    New_Field_Association
                      (Domain => EW_Term,
                       Field  => +E_Symb (Root, WNE_Rec_Extension),
                       Value  => New_Call (Domain => EW_Term,
                                           Name   =>
                                             To_Ident (WNE_Hide_Extension),
                                           Args   => Args));
               end;
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

      --  Step 3. Copy the tag field of tagged types

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

      --  Step 4. Copy the is_moved field if the type has ownership

      if Has_Ownership_Annotation (E) and then Needs_Reclamation (E) then
         From_Index := From_Index + 1;
         From_Root_Aggr (From_Index) :=
           New_Field_Association
             (Domain => EW_Term,
              Field  => To_Local (E_Symb (E, WNE_Is_Moved_Field)),
              Value  => New_Record_Access
                (Name  => +R_Ident,
                 Field => +E_Symb (Root, WNE_Is_Moved_Field),
                 Typ   => EW_Bool_Type));

         To_Index := To_Index + 1;
         To_Root_Aggr (To_Index) :=
           New_Field_Association
             (Domain => EW_Term,
              Field  => +E_Symb (Root, WNE_Is_Moved_Field),
              Value  => New_Record_Access
                (Name  => +A_Ident,
                 Field => To_Local (E_Symb (E, WNE_Is_Moved_Field)),
                 Typ   => EW_Bool_Type));
      end if;

      pragma Assert (To_Root_Aggr'Last = To_Index);
      pragma Assert (From_Root_Aggr'Last = From_Index);

      Emit
        (Th,
         New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => To_Local (E_Symb (E, WNE_To_Base)),
            Binders     => R_Binder,
            Location    => No_Location,
            Labels      => Symbol_Sets.Empty_Set,
            Return_Type =>
              EW_Abstract (Root, Relaxed_Init => Init_Wrapper),
            Def         =>
              New_Record_Aggregate
                (Associations => To_Root_Aggr)));
      Emit
        (Th,
         New_Function_Decl
           (Domain      => EW_Pterm,
            Name        => To_Local (E_Symb (E, WNE_Of_Base)),
            Binders     => From_Binder,
            Location    => No_Location,
            Labels      => Symbol_Sets.Empty_Set,
            Return_Type => Abstr_Ty,
            Def         =>
              New_Record_Aggregate
                (Associations => From_Root_Aggr)));

   end Declare_Conversion_Functions;

   -------------------------------------
   -- Declare_Init_Wrapper_For_Record --
   -------------------------------------

   procedure Declare_Init_Wrapper_For_Record
     (Th : Theory_UC;
      E  : Entity_Id)
   is

      procedure Declare_Wrapper_Conversions;
      --  Declare conversion functions to and from the wrapper type

      Name      : constant W_Name_Id :=
        To_Why_Type (E, Local => True, Relaxed_Init => True);
      Root      : constant Entity_Id     := Root_Retysp (E);
      Is_Root   : constant Boolean       := Root = E;
      Abstr_Ty  : constant W_Type_Id     := New_Named_Type (Name => Name);

      A_Ident   : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Abstr_Ty);
      A_Binder  : constant Binder_Array :=
        (1 => (B_Name => A_Ident,
               others => <>));

      ---------------------------------
      -- Declare_Wrapper_Conversions --
      ---------------------------------

      procedure Declare_Wrapper_Conversions is
         Num_Discrs        : constant Natural := Count_Discriminants (E);
         Num_Fields        : constant Natural := Count_Why_Regular_Fields (E);
         Num_All           : constant Natural :=
           Count_Why_Top_Level_Fields (E);
         To_Wrapper_Aggr   : W_Field_Association_Array (1 .. Num_All);
         From_Wrapper_Aggr : W_Field_Association_Array (1 .. Num_All);
         Index             : Natural := 0;

         X_Ident         : constant W_Identifier_Id :=
           New_Identifier (Name => "x", Typ => EW_Abstract (E));
         X_Binder     : constant Binder_Array :=
           (1 => (B_Name => X_Ident,
                  others => <>));
      begin
         --  Step 1. We do not need conversions for discriminants, as we never
         --  use wrapper types for them.

         if Num_Discrs > 0 then
            declare
               Discrs_Comp    : constant W_Identifier_Id :=
                 E_Symb (E, WNE_Rec_Split_Discrs);
               A_Discr_Access : constant W_Expr_Id :=
                 New_Record_Access (Name  => +A_Ident,
                                    Field => To_Ident (WNE_Rec_Split_Discrs));
               X_Discr_Access : constant W_Expr_Id :=
                 New_Record_Access (Name  => +X_Ident,
                                    Field => Discrs_Comp);
            begin
               Index := Index + 1;
               To_Wrapper_Aggr (Index) :=
                 New_Field_Association
                   (Domain => EW_Term,
                    Field  => To_Ident (WNE_Rec_Split_Discrs),
                    Value  => X_Discr_Access);
               From_Wrapper_Aggr (Index) :=
                 New_Field_Association
                   (Domain => EW_Term,
                    Field  => Discrs_Comp,
                    Value  => A_Discr_Access);
            end;
         end if;

         --  Step 2. For fields, we convert each component to and from the
         --  wrapper type.

         if Num_Fields > 0 then
            declare
               To_Wrapper_Field   :
                  W_Field_Association_Array (1 .. Num_Fields);
               From_Wrapper_Field :
                  W_Field_Association_Array (1 .. Num_Fields);
               Fields_Comp        : constant W_Identifier_Id :=
                 E_Symb (E, WNE_Rec_Split_Fields);
               A_Field_Access     : constant W_Expr_Id :=
                 New_Record_Access (Name  => +A_Ident,
                                    Field => To_Ident (WNE_Rec_Split_Fields));
               X_Field_Access     : constant W_Expr_Id :=
                 New_Record_Access (Name  => +X_Ident,
                                    Field => Fields_Comp);
               Field_Index        : Natural := 0;

            begin
               for Field of Get_Component_Set (E) loop
                  declare
                     Field_Id      : constant W_Identifier_Id :=
                       To_Why_Id (Field, Rec => E);
                     Field_Ty      : constant W_Type_Id :=
                       (if Field = E
                        then New_Named_Type
                          (Name => Get_Name (E_Symb (E, WNE_Private_Type)))
                        else W_Type_Of_Component
                          (Field, E, Init_Wrapper => False));
                     --  Normal type for the field. If Field stands for the
                     --  private part of E (Field = E) then we cannot use
                     --  W_Type_Of_Component to get this type, as it always
                     --  returns a local name for this private part, and here
                     --  the private part is not local.

                     Field_Wrapper : constant W_Type_Id := W_Type_Of_Component
                       (Field, E, Init_Wrapper =>
                          Has_Init_Wrapper (Etype (Field)));
                     --  Wrapper type for the field

                  begin
                     Field_Index := Field_Index + 1;

                     --  Add of_wrapper a.field to From_Wrapper_Field

                     declare
                        A_Access      : constant W_Expr_Id :=
                          New_Record_Access
                            (Name  => A_Field_Access,
                             Field => To_Local (Field_Id),
                             Typ   => Field_Wrapper);
                        Conv_A_Access : constant W_Expr_Id :=
                          (if Is_Type (Field)
                           then New_Call
                             (Domain => EW_Term,
                              Name   =>
                                (if Field = E
                                 then To_Local
                                   (E_Symb (Field, WNE_Private_Of_Wrapper))
                                 else E_Symb (Field, WNE_Private_Of_Wrapper)),
                              Args   => (1 => A_Access),
                              Typ    => Field_Ty)
                           else Insert_Simple_Conversion
                             (Domain         => EW_Term,
                              To             => Field_Ty,
                              Expr           => A_Access,
                              Force_No_Slide => True));
                        --  If the field stand for the private part of a type,
                        --  call the corresponding Private_Of_Wrapper function.
                        --  Otherwise, introduce a conversion.

                     begin
                        From_Wrapper_Field (Field_Index) :=
                          New_Field_Association
                            (Domain => EW_Term,
                             Field  => Field_Id,
                             Value  => Conv_A_Access);
                     end;

                     --  Add to_wrapper a.field to To_Wrapper_Field

                     declare
                        X_Access      : constant W_Expr_Id :=
                          New_Record_Access
                            (Name  => X_Field_Access,
                             Field => Field_Id,
                             Typ   => Field_Ty);
                        Conv_X_Access : constant W_Expr_Id :=
                          (if Is_Type (Field)
                           then New_Call
                             (Domain => EW_Term,
                              Name   =>
                                (if Field = E
                                 then To_Local
                                   (E_Symb (Field, WNE_Private_To_Wrapper))
                                 else E_Symb (Field, WNE_Private_To_Wrapper)),
                              Args   => (1 => X_Access),
                              Typ    => Field_Wrapper)
                           else Insert_Simple_Conversion
                             (Domain         => EW_Term,
                              To             => Field_Wrapper,
                              Expr           => X_Access,
                              Force_No_Slide => True));
                        --  If the field stand for the private part of a type,
                        --  call the corresponding Private_To_Wrapper function.
                        --  Otherwise, introduce a conversion.

                     begin
                        To_Wrapper_Field (Field_Index) :=
                          New_Field_Association
                            (Domain => EW_Term,
                             Field  => To_Local (Field_Id),
                             Value  => Conv_X_Access);
                     end;
                  end;
               end loop;

               pragma Assert (Field_Index = Num_Fields);
               Index := Index + 1;
               From_Wrapper_Aggr (Index) :=
                 New_Field_Association
                   (Domain => EW_Term,
                    Field  => Fields_Comp,
                    Value  => New_Record_Aggregate
                      (Associations => From_Wrapper_Field));
               To_Wrapper_Aggr (Index) :=
                 New_Field_Association
                   (Domain => EW_Term,
                    Field  => To_Ident (WNE_Rec_Split_Fields),
                    Value  => New_Record_Aggregate
                      (Associations => To_Wrapper_Field));
            end;
         end if;

         --  Step 3. Copy the is_moved field if the type has ownership

         if Has_Ownership_Annotation (E) and then Needs_Reclamation (E) then
            declare
               Moved_Comp    : constant W_Identifier_Id :=
                 E_Symb (E, WNE_Is_Moved_Field);
               A_Moved_Access : constant W_Expr_Id :=
                 New_Record_Access (Name  => +A_Ident,
                                    Field => To_Ident (WNE_Is_Moved_Field));
               X_Moved_Access : constant W_Expr_Id :=
                 New_Record_Access (Name  => +X_Ident,
                                    Field => Moved_Comp);
            begin
               Index := Index + 1;
               To_Wrapper_Aggr (Index) :=
                 New_Field_Association
                   (Domain => EW_Term,
                    Field  => To_Ident (WNE_Is_Moved_Field),
                    Value  => X_Moved_Access);
               From_Wrapper_Aggr (Index) :=
                 New_Field_Association
                   (Domain => EW_Term,
                    Field  => Moved_Comp,
                    Value  => A_Moved_Access);
            end;
         end if;

         pragma Assert (Index = Num_All);

         Emit
           (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_Of_Wrapper)),
               Binders     => A_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => EW_Abstract (E),
               Def         =>
                 New_Record_Aggregate
                   (Associations => From_Wrapper_Aggr)));
         Emit
           (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_To_Wrapper)),
               Binders     => X_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         =>
                 New_Record_Aggregate
                   (Associations => To_Wrapper_Aggr)));
      end Declare_Wrapper_Conversions;

   --  Start of processing for Declare_Init_Wrapper_For_Record

   begin
      --  This type is simply a copy of an existing type, we re-export the
      --  corresponding module and then return.

      if Oldest_Parent_With_Same_Fields (E) /= E then

         declare
            Clone : constant Entity_Id := Oldest_Parent_With_Same_Fields (E);
         begin
            Add_With_Clause (Th, E_Init_Module (Clone), EW_Export);

            --  If the copy has the same name as the original, do not redefine
            --  the type name.

            if Short_Name (E) /= Short_Name (Clone) then
               Emit (Th,
                     New_Type_Decl
                       (Name  => Name,
                        Alias =>
                          +New_Named_Type
                          (Name => To_Why_Type
                             (Clone, Local => True, Relaxed_Init => True))));
            end if;
         end;
         return;

      --  If E is an empty record, the wrapper is a copy of its underlying
      --  type. We re-export the corresponding module and then return.

      elsif Count_Why_Top_Level_Fields (E) = 0 then

         Add_With_Clause (Th, E_Module (E), EW_Export);

         Emit (Th,
               New_Type_Decl
                 (Name  => Name,
                  Alias =>
                    +New_Named_Type
                    (Name => To_Why_Type (E, Local => True))));

         --  Declare dummy conversion functions that will be used to convert
         --  between wrapper and concrete types.

         Emit
           (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_Of_Wrapper)),
               Binders     => A_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         => +A_Ident));
         Emit
           (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_To_Wrapper)),
               Binders     => A_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         => +A_Ident));
         return;

      --  Simple private types are translated as an abstract type. Introduce
      --  an init flag for it.

      elsif Is_Simple_Private_Type (E) then
         Declare_Simple_Wrapper_Type
           (Th           => Th,
            W_Nam        => To_Why_Type
              (E, Local => True, Relaxed_Init => True),
            Init_Val     => To_Local (E_Symb (E, WNE_Init_Value)),
            Attr_Init    => To_Local (E_Symb (E, WNE_Attr_Init)),
            Of_Wrapper   => To_Local (E_Symb (E, WNE_Of_Wrapper)),
            To_Wrapper   => To_Local (E_Symb (E, WNE_To_Wrapper)),
            Dummy        => To_Local (E_Symb (E, WNE_Dummy)),
            Default_Init =>
              Default_Initialization (E) = Full_Default_Initialization);
      end if;

      --  Introduce a wrapper for the private part of E if there is one

      if Has_Private_Part (E) and then not Is_Simple_Private_Type (E) then
         Declare_Simple_Wrapper_Type
           (Th           => Th,
            W_Nam        => To_Local (E_Symb (E, WNE_Private_Type)),
            Init_Val     => To_Local (E_Symb (E, WNE_Init_Value)),
            Attr_Init    => To_Local (E_Symb (E, WNE_Attr_Init)),
            Of_Wrapper   => To_Local (E_Symb (E, WNE_Private_Of_Wrapper)),
            To_Wrapper   => To_Local (E_Symb (E, WNE_Private_To_Wrapper)),
            Dummy        => To_Local (E_Symb (E, WNE_Private_Dummy)),
            Default_Init =>
              Default_Initialization (E) = Full_Default_Initialization);
      end if;

      Declare_Record_Type
        (Th           => Th,
         E            => E,
         Root         => Root,
         Ty_Name      => Name,
         Reuse_Discr  => True,
         Init_Wrapper => True);

      Declare_Protected_Access_Functions
        (Th           => Th,
         E            => E,
         Root         => Root,
         Ty_Name      => Name,
         Reuse_Discr  => True,
         Init_Wrapper => True);

      --  We need to delare conversion functions before the protected access
      --  functions, because the former may be used in the latter

      if not Is_Root then
         pragma Assert (not Is_Simple_Private_Type (E));

         Declare_Conversion_Functions
           (Th           => Th,
            E            => E,
            Root         => Root,
            Ty_Name      => Name,
            Init_Wrapper => True);

      else
         --  Declare dummy conversion functions that will be used to convert
         --  other types which use E as a representative type.

         Emit
           (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_To_Base)),
               Binders     => A_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         => +A_Ident));
         Emit
           (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_Of_Base)),
               Binders     => A_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         => +A_Ident));
      end if;

      --  For simple private types, wrapper conversion functions have already
      --  been defined. Otherwise, define them now.

      if not Is_Simple_Private_Type (E) then
         Declare_Wrapper_Conversions;
      end if;
   end Declare_Init_Wrapper_For_Record;

   ----------------------------------------
   -- Declare_Protected_Access_Functions --
   ----------------------------------------

   procedure Declare_Protected_Access_Functions
     (Th           : Theory_UC;
      E            : Entity_Id;
      Root         : Entity_Id;
      Ty_Name      : W_Name_Id;
      Reuse_Discr  : Boolean;
      Init_Wrapper : Boolean)
   is
      Comp_Info : constant Component_Info_Map := Get_Variant_Info (E);
      Abstr_Ty  : constant W_Type_Id     := New_Named_Type (Name => Ty_Name);

      A_Ident   : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Abstr_Ty);
      R_Binder  : constant Binder_Array :=
        (1 => (B_Name => A_Ident,
               others => <>));

      procedure Declare_Protected_Access_Function (Field : Entity_Id);
      --  Declare a program access function for a field, whose precondition
      --  is Discriminant_Check_Pred_Name. Note that [Precond] has been
      --  computed so that it uses the correct predicate name, whether it
      --  has been defined here or in the root type. In the case of a
      --  discriminant, the precondition is simply "true".
      --  @param Field a record field or disciminant.

      function Compute_Discriminant_Check (Field : Entity_Id) return W_Pred_Id;
      --  Compute the discriminant check for an access to the given field, as a
      --  predicate which can be used as a precondition.

      function Compute_Others_Choice
        (Info  : Component_Info;
         Discr : W_Term_Id)
         return W_Pred_Id;
      --  Compute (part of) the discriminant check for one discriminant in the
      --  special case where the N_Discrete_Choice is actually an
      --  N_Others_Choice.

      function Transform_Discrete_Choices
        (Case_N : Node_Id;
         Expr   : W_Term_Id)
         return W_Pred_Id;
      --  Wrapper for the function in Gnat2Why.Expr

      --------------------------------
      -- Compute_Discriminant_Check --
      --------------------------------

      function Compute_Discriminant_Check (Field : Entity_Id) return W_Pred_Id
      is
         Info : Component_Info := Get_Component_Info (Comp_Info, Field);
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
                       Field => To_Why_Id
                         (Ada_Discr, Local => not Reuse_Discr, Rec => Root),
                       Typ   => EW_Abstract (Etype (Ada_Discr))));
               New_Cond  : constant W_Pred_Id :=
                 (if Is_Others_Choice (Discrete_Choices (Info.Parent_Variant))
                  then
                    Compute_Others_Choice (Info, Discr)
                  else
                    +Transform_Discrete_Choices (Info.Parent_Variant, Discr));
            begin
               Cond :=
                 +New_And_Then_Expr
                   (Domain => EW_Pred,
                    Left   => +Cond,
                    Right  => +New_Cond);
               Info := Get_Component_Info (Comp_Info, Info.Parent_Var_Part);
            end;
         end loop;

         return Cond;
      end Compute_Discriminant_Check;

      ---------------------------
      -- Compute_Others_Choice --
      ---------------------------

      function Compute_Others_Choice
        (Info  : Component_Info;
         Discr : W_Term_Id)
         return W_Pred_Id
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

      ---------------------------------------
      -- Declare_Protected_Access_Function --
      ---------------------------------------

      procedure Declare_Protected_Access_Function (Field : Entity_Id) is
         Why_Name  : constant W_Identifier_Id :=
           (if not Reuse_Discr or else Ekind (Field) /= E_Discriminant then
                 To_Why_Id (Field, Local => True, Rec => E)
            else To_Why_Id (Field, Rec => Root));
         Prog_Name : constant W_Identifier_Id :=
           To_Program_Space (To_Why_Id (Field, Local => True, Rec => E));
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
           (if Ekind (Field) /= E_Component then True_Pred
            else Discriminant_Check_Pred_Call (E, Field, A_Ident));
      begin
         Emit (Th,
               New_Function_Decl
                 (Domain      => EW_Prog,
                  Name        => Prog_Name,
                  Binders     => R_Binder,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Return_Type => W_Type_Of_Component
                    (Field, E, Init_Wrapper),
                  Pre         => Precond,
                  Post        => Post));
      end Declare_Protected_Access_Function;

      --------------------------------
      -- Transform_Discrete_Choices --
      --------------------------------

      function Transform_Discrete_Choices
        (Case_N : Node_Id;
         Expr   : W_Term_Id)
         return W_Pred_Id
      is
      begin
         return Gnat2Why.Expr.Transform_Discrete_Choices
           (Choices      => Discrete_Choices (Case_N),
            Choice_Type  => Empty,  --  not used for predicates, can be empty
            Matched_Expr => Expr,
            Params       => Logic_Params);
      end Transform_Discrete_Choices;

   --  Start of processing for Declare_Protected_Access_Functions

   begin
      if Is_Simple_Private_Type (E) then
         return;
      end if;

      --  Generate program access functions for discriminants
      --  ??? enrich the postcondition of access to discriminant, whenever
      --  we statically know its value (in case of E_Record_Subtype)

      if Has_Discriminants (E) then
         declare
            Discr : Entity_Id := First_Discriminant (E);
         begin
            loop
               Declare_Protected_Access_Function (Discr);
               Next_Discriminant (Discr);
               exit when No (Discr);
            end loop;
         end;
      end if;

      for Field of Get_Component_Set (E) loop

         --  We generate a discriminant check predicate.
         --  ??? maybe only do that if the type has discriminants

         if Ekind (Field) = E_Component then
            declare
               Pred_Name : constant W_Identifier_Id :=
                 Discriminant_Check_Pred_Name (E, Field, True);
               Pre_Cond  : constant W_Pred_Id :=
                 Compute_Discriminant_Check (Field);
            begin
               Emit (Th,
                     New_Function_Decl
                       (Domain   => EW_Pred,
                        Name     => Pred_Name,
                        Binders  => R_Binder,
                        Location => No_Location,
                        Labels   => Symbol_Sets.Empty_Set,
                        Def      => +Pre_Cond));
            end;
         end if;

         --  We generate the program access function.

         Declare_Protected_Access_Function (Field);
      end loop;
   end Declare_Protected_Access_Functions;

   -------------------------
   -- Declare_Record_Type --
   -------------------------

   procedure Declare_Record_Type
     (Th           : Theory_UC;
      E            : Entity_Id;
      Root         : Entity_Id;
      Ty_Name      : W_Name_Id;
      Reuse_Discr  : Boolean;
      Init_Wrapper : Boolean)
   is
      Num_Discrs : constant Natural := Count_Discriminants (E);
      Num_Fields : constant Natural := Count_Why_Regular_Fields (E);
      Num_All    : constant Natural := Count_Why_Top_Level_Fields (E);

      Binders_D  : Binder_Array (1 .. Num_Discrs);
      Binders_F  : Binder_Array (1 .. Num_Fields);
      Binders_A  : Binder_Array (1 .. Num_All);
      Index      : Positive := 1;
      Index_All  : Positive := 1;

   begin

      --  Hardcoded types are translated separately

      if Is_Hardcoded_Entity (E) then

         --  Hardcoded types are necessarily simple private types

         pragma Assert (Is_Simple_Private_Type (E));
         Emit_Hardcoded_Type_Declaration (Th, E);

         --  Simple private types are translated directly as abstract types

      elsif Is_Simple_Private_Type (E) then
         Emit (Th,
               New_Type_Decl
                 (Name => To_String (WNE_Rec_Rep)));
      else

         --  Generate a record type for E's discriminants if Reuse_Discr is
         --  False and use Root's record type for discriminants otherwise.

         if Num_Discrs > 0 then
            declare
               Discr_Name : constant W_Name_Id :=
                 To_Name (WNE_Rec_Split_Discrs);
               Discr      : Entity_Id := First_Discriminant (E);
            begin
               if not Reuse_Discr then
                  loop
                     Binders_D (Index) :=
                       (B_Name   =>
                          To_Why_Id
                            (Discr,
                             Local => True,
                             Rec   => Root,
                             Typ   => EW_Abstract (Etype (Discr))),
                        Labels   =>
                          Get_Model_Trace_Label
                            (E               => Discr,
                             Is_Record_Field => True),
                        Ada_Node => Discr,
                        others   => <>);
                     Index := Index + 1;
                     Next_Discriminant (Discr);
                     exit when No (Discr);
                  end loop;

                  Emit_Record_Declaration
                    (Th           => Th,
                     Name         => Discr_Name,
                     Binders      => Binders_D,
                     SPARK_Record => True);

                  --  Generate a mutable record to hold elements of type
                  --  __split_discrs, as well as an havoc function for it.

                  Emit_Ref_Type_Definition (Th   => Th,
                                            Name => Discr_Name);
                  Emit
                    (Th,
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
                              (if Reuse_Discr then Get_Name
                                 (E_Symb (Root, WNE_Rec_Split_Discrs))
                               else Discr_Name),
                            Is_Mutable => False)),
                  others => <>);
               Index_All := Index_All + 1;
            end;
         end if;

         --  Generate a record type for E's normal components. This
         --  includes:
         --    . visible components of the type
         --    . invisible components of parents in a derived type

         if Num_Fields > 0
           or else Is_Tagged_Type (E)
         then
            Index := 1;

            for Field of Get_Component_Set (E) loop
               Binders_F (Index) :=
                 (B_Name   =>
                    To_Why_Id
                      (Field,
                       Rec   => E,
                       Local => True,
                       Typ   => W_Type_Of_Component
                         (Field, E, Init_Wrapper)),
                  Labels   =>
                    Get_Model_Trace_Label
                      (E               => Field,
                       Is_Record_Field => True),
                  Ada_Node => Field,
                  others   => <>);
               Index := Index + 1;
            end loop;

            --  For tagged types, add a field of the local abstract __exp_type
            --  type representing the unknown extension components.

            if Is_Tagged_Type (E) then
               Binders_F (Index) :=
                 (B_Name => New_Identifier
                    (Domain => EW_Term,
                     Name   => To_Local (E_Symb (E, WNE_Rec_Extension)),
                     Typ    => New_Named_Type
                       (To_Local (E_Symb (E, WNE_Extension_Type)))),
                  others => <>);
               Index := Index + 1;
            end if;

            pragma Assert (Index = Binders_F'Last + 1);

            Emit_Record_Declaration (Th           => Th,
                                     Name         =>
                                       To_Name (WNE_Rec_Split_Fields),
                                     Binders      => Binders_F,
                                     SPARK_Record => True);

            --  Generate a mutable record to hold elements of type
            --  __split_fields, as well as an havoc function for it.

            Emit_Ref_Type_Definition
              (Th   => Th,
               Name => To_Name (WNE_Rec_Split_Fields));
            Emit
              (Th,
               New_Havoc_Declaration (To_Name (WNE_Rec_Split_Fields)));

            Binders_A (Index_All) :=
              (B_Name   =>
                 New_Identifier (Ada_Node => Empty,
                                 Name     =>
                                   To_String (WNE_Rec_Split_Fields),
                                 Typ      =>
                                   New_Type
                                     (Type_Kind  => EW_Abstract,
                                      Name       =>
                                        To_Name (WNE_Rec_Split_Fields),
                                      Is_Mutable => False)),
               others   => <>);
            Index_All := Index_All + 1;
         end if;

         --  For tagged types, add a tag field of type int

         if Is_Tagged_Type (E) then
            Binders_A (Index_All) :=
              (B_Name => To_Local (E_Symb (E, WNE_Attr_Tag)),
               others => <>);
            Index_All := Index_All + 1;
         end if;

         --  For private types with ownership, add a boolean is_moved flag

         if Has_Ownership_Annotation (E) and then Needs_Reclamation (E) then
            Binders_A (Index_All) :=
              (B_Name => To_Local (E_Symb (E, WNE_Is_Moved_Field)),
               others => <>);
            Index_All := Index_All + 1;
         end if;

         pragma Assert (Index_All = Num_All + 1);

         Emit_Record_Declaration (Th           => Th,
                                  Name         => Ty_Name,
                                  Binders      => Binders_A,
                                  SPARK_Record => True);
      end if;
   end Declare_Record_Type;

   -----------------------------
   -- Declare_Rep_Record_Type --
   -----------------------------

   procedure Declare_Rep_Record_Type
     (Th : Theory_UC;
      E : Entity_Id)
   is
      procedure Declare_Equality_Function;
      --  Generate the boolean equality function for the record type

      procedure Declare_Extraction_Functions (Components : Node_Lists.List);
      --  @param Components the list of components to hide

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

      ---------------------
      -- Local Variables --
      ---------------------

      Root      : constant Entity_Id     := Root_Retysp (E);
      Is_Root   : constant Boolean       := Root = E;
      Ty_Name   : constant W_Name_Id     := To_Name (WNE_Rec_Rep);
      Abstr_Ty  : constant W_Type_Id     := New_Named_Type (Name => Ty_Name);

      A_Ident   : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Abstr_Ty);
      R_Binder  : constant Binder_Array :=
        (1 => (B_Name => A_Ident,
               others => <>));

      -------------------------------
      -- Declare_Equality_Function --
      -------------------------------

      procedure Declare_Equality_Function is

         B_Ident : constant W_Identifier_Id :=
           New_Identifier (Name => "b", Typ => Abstr_Ty);

         function First_Parent_With_User_Defined_Eq
           (Ty : Type_Kind_Id) return Opt_Type_Kind_Id
           with Post =>
             (if Present (First_Parent_With_User_Defined_Eq'Result)
              then Present
                (Get_User_Defined_Eq
                   (First_Parent_With_User_Defined_Eq'Result)));
         --  Traverse the parents of Ty to find a type with a user-defined
         --  equality.

         function New_Field_Access
           (Is_Discr   : Boolean;
            Name       : W_Term_Id;
            Field_Id   : W_Identifier_Id;
            Field_Type : Entity_Id) return W_Term_Id;
         --  Generate Name.Field_Id with no Init wrappers

         function New_Field_Equality
           (Is_Discr               : Boolean;
            Field_Id, Enclosing_Id : W_Identifier_Id;
            Is_Private             : Boolean;
            Field_Type             : Entity_Id)
            return W_Pred_Id;
         --  @param Is_Discr true if the field is a discriminant
         --  @param Field_Id why id for a component or discriminant
         --  @param Enclosing_Id why id for the appropriate top level why
         --         record field
         --  @param Is_Private True if the component should be translated as
         --         private in Why
         --  @param Field_Type Ada type of the component, it is the enclosing
         --         type if Is_Private is True
         --  @return Equality of field_id from A and B.

         ---------------------------------------
         -- First_Parent_With_User_Defined_Eq --
         ---------------------------------------

         function First_Parent_With_User_Defined_Eq
           (Ty : Type_Kind_Id) return Opt_Type_Kind_Id
         is
            Parent : Entity_Id := Ty;
         begin
            loop
               --  Go to the base type of the parent

               Parent := Parent_Retysp (Parent);
               if Present (Parent) then
                  Parent := Base_Retysp (Parent);
               end if;

               if No (Parent)
                 or else Present (Get_User_Defined_Eq (Parent))
               then
                  return Parent;
               end if;
            end loop;
         end First_Parent_With_User_Defined_Eq;

         ----------------------
         -- New_Field_Access --
         ----------------------

         function New_Field_Access
           (Is_Discr   : Boolean;
            Name       : W_Term_Id;
            Field_Id   : W_Identifier_Id;
            Field_Type : Entity_Id) return W_Term_Id
         is
           (if Is_Discr
            or else not SPARK_Definition.Has_Relaxed_Init (Field_Type)
            then New_Record_Access
              (Name  => Name,
               Field => Field_Id,
               Typ   => EW_Abstract (Field_Type))
            else Insert_Simple_Conversion
              (Ada_Node       => Empty,
               Expr           => New_Record_Access
                 (Name  => Name,
                  Field => Field_Id,
                  Typ   => EW_Abstract
                    (Field_Type, Relaxed_Init => True)),
               To             => EW_Abstract (Field_Type),
               Force_No_Slide => True));

         ------------------------
         -- New_Field_Equality --
         ------------------------

         function New_Field_Equality
           (Is_Discr               : Boolean;
            Field_Id, Enclosing_Id : W_Identifier_Id;
            Is_Private             : Boolean;
            Field_Type             : Entity_Id)
            return W_Pred_Id
         is
            A_Access : constant W_Expr_Id :=
              New_Record_Access (Name  => +A_Ident,
                                 Field => Enclosing_Id);
            B_Access : constant W_Expr_Id :=
              New_Record_Access (Name  => +B_Ident,
                                 Field => Enclosing_Id);
         begin
            if Is_Private then
               declare
                  Priv_Name : constant W_Identifier_Id :=
                    E_Symb (Field_Type, WNE_Private_Eq);
               begin

                  --  For equality over private components, use an abstract
                  --  logic function.

                  return
                    New_Call
                      (Name => (if Field_Type = E then To_Local (Priv_Name)
                                else Priv_Name),
                       Typ  => EW_Bool_Type,
                       Args => (1 => New_Record_Access
                                (Name  => A_Access,
                                 Field => Field_Id,
                                 Typ   => EW_Private_Type),
                                2 => New_Record_Access
                                  (Name  => B_Access,
                                   Field => Field_Id,
                                   Typ   => EW_Private_Type)));
               end;
            else
               declare
                  A_F_Access : constant W_Term_Id := New_Field_Access
                    (Is_Discr, +A_Access, Field_Id, Field_Type);
                  B_F_Access : constant W_Term_Id := New_Field_Access
                    (Is_Discr, +B_Access, Field_Id, Field_Type);

               begin
                  return +New_Ada_Equality
                    (Typ    => Field_Type,
                     Domain => EW_Pred,
                     Left   => +A_F_Access,
                     Right  => +B_F_Access);
               end;
            end if;
         end New_Field_Equality;

      --  Start of processing for Declare_Equality_Function

      begin
         --  For a record type:
         --
         --    type R (D1 : T_D1; ...) is record
         --      F1 : T_F1;
         --      ...
         --    end record;
         --
         --  We generate:
         --
         --    function bool_eq (a: __rep) (b: __rep) : bool =
         --      T_D1.<ada_eq> a.__split_discrs.d1 b.__split_discrs.d1
         --   /\ ...
         --   /\ T_F1.<ada_eq> a.__split_fields.f1 b.__split_fields.f1
         --   /\ ...
         --
         --  Where <ada_eq> is the primitive equality on record types and the
         --  predefined one on other types.
         --
         --  On tagged record extensions, if there is a parent type on which
         --  the primitive equality is redefined, we should use it. We
         --  generate:
         --
         --   function bool_eq (a: __rep) (b: __rep) : bool =
         --     Parent.user_eq
         --       { __split_fields =
         --         { parent_f1 = a.__split_fields.parent_f1;
         --           ... } ;
         --        attr__tag = parent.__tag }
         --       { __split_fields =
         --         { parent_f1 = b.__split_fields.parent_f1;
         --           ... } ;
         --        attr__tag = parent.__tag }
         --     /\ <ada_eq> a.__split_fields.new_f1 b.__split_fields.new_f1
         --     /\ ...

         if not Is_Limited_View (E) then
            declare
               Condition      : W_Pred_Id := True_Pred;
               Parent_With_Eq : constant Opt_Type_Kind_Id :=
                 (if Is_Tagged_Type (E)
                  then First_Parent_With_User_Defined_Eq (E)
                  else Empty);
               Nb_Anc_Fields  : constant Natural :=
                 (if Present (Parent_With_Eq)
                  then Natural (Get_Component_Set (Parent_With_Eq).Length)
                  else 0);
               A_Anc_Fields   : W_Field_Association_Array (1 .. Nb_Anc_Fields);
               B_Anc_Fields   : W_Field_Association_Array (1 .. Nb_Anc_Fields);
               --  Field associations for the equality on the part of E
               --  corresponding to elements of Parent_With_Eq if any.

            begin
               --  Compare discriminants. We only do it if Parent_With_Eq is
               --  Empty, as otherwise, discriminants will be checked as part
               --  of the ancestor part of E (in SPARK discriminants cannot be
               --  added in record extensions).

               if Has_Discriminants (E) and then No (Parent_With_Eq) then
                  declare
                     Discrs_Id : constant W_Identifier_Id :=
                       To_Ident (WNE_Rec_Split_Discrs);
                     Discr     : Entity_Id := First_Discriminant (E);
                  begin
                     loop
                        declare
                           Discr_Id   : constant W_Identifier_Id :=
                             (if Is_Root then
                                 To_Why_Id (Discr, Local => True, Rec => E)
                              else To_Why_Id (Discr, Rec => Root));
                           Comparison : constant W_Pred_Id :=
                             New_Field_Equality
                               (Is_Discr     => True,
                                Field_Id     => Discr_Id,
                                Enclosing_Id => Discrs_Id,
                                Is_Private   => False,
                                Field_Type   => Retysp (Etype (Discr)));
                        begin
                           Condition :=
                             +New_And_Then_Expr
                             (Domain => EW_Pred,
                              Left   => +Condition,
                              Right  => +Comparison);
                        end;
                        Next_Discriminant (Discr);
                        exit when No (Discr);
                     end loop;
                  end;
               end if;

               --  Compare Fields. We aggregate the equalities for the new
               --  fields of E in Conjuncts, and we store the associations for
               --  the ancestor part of E in A_Anc_Fields and B_Anc_Fields.

               if not Is_Simple_Private_Type (E) then
                  declare
                     Comp_Set : Component_Sets.Set renames
                       Get_Component_Set (E);
                  begin
                     if not Comp_Set.Is_Empty then
                        declare
                           Conjuncts    : W_Pred_Array
                             (1 .. Positive (Comp_Set.Length) - Nb_Anc_Fields);
                           Conj_I       : Natural := 0;
                           Fields_Id    : constant W_Identifier_Id :=
                             To_Ident (WNE_Rec_Split_Fields);
                           Anc_Fields_I : Natural := 0;

                        begin
                           for Comp of Comp_Set loop
                              declare
                                 Field_Id    : constant W_Identifier_Id :=
                                   To_Why_Id (Comp, Local => True, Rec => E);
                                 Parent_Comp : constant Entity_Id :=
                                   (if Present (Parent_With_Eq)
                                    then Search_Component_In_Type
                                      (Parent_With_Eq, Comp)
                                    else Empty);

                              begin
                                 --  If there is no component corresponding to
                                 --  Comp in Parent_With_Eq, it is a new
                                 --  component. Add the corresponding equality
                                 --  to Conjuncts.

                                 if No (Parent_Comp) then
                                    declare
                                       Comparison     : constant W_Pred_Id :=
                                         New_Field_Equality
                                           (Is_Discr     => False,
                                            Field_Id     => Field_Id,
                                            Enclosing_Id => Fields_Id,
                                            Is_Private   => Is_Type (Comp),
                                            Field_Type   =>
                                              (if Is_Type (Comp) then
                                                    Comp
                                               else Retysp (Etype (Comp))));
                                       Always_Present : constant Boolean :=
                                         not Has_Discriminants (E)
                                         or else Ekind (Comp) /= E_Component;
                                    begin
                                       Conj_I := Conj_I + 1;
                                       Conjuncts (Conj_I) :=
                                         (if Always_Present then Comparison
                                          else
                                             New_Connection
                                            (Op     => EW_Imply,
                                             Left   =>
                                               Discriminant_Check_Pred_Call
                                                 (E, Comp, A_Ident),
                                             Right  => Comparison));
                                    end;

                                 --  Otherwise, Comp comes from Parent_With_Eq.
                                 --  Store an association for it in
                                 --  A_Anc_Fields and B_Anc_Fields.

                                 else
                                    Anc_Fields_I := Anc_Fields_I + 1;
                                    A_Anc_Fields (Anc_Fields_I) :=
                                      New_Field_Association
                                        (Domain => EW_Term,
                                         Field  => To_Why_Id
                                           (Parent_Comp,
                                            Rec => Parent_With_Eq),
                                         Value  => +Insert_Simple_Conversion
                                           (Expr           => New_Field_Access
                                              (Is_Discr   => False,
                                               Name       => New_Record_Access
                                                 (Name  => +A_Ident,
                                                  Field => Fields_Id),
                                               Field_Id   => Field_Id,
                                               Field_Type =>
                                                 Retysp (Etype (Comp))),
                                            To             => EW_Abstract
                                              (Etype (Parent_Comp)),
                                            Force_No_Slide => True));
                                    B_Anc_Fields (Anc_Fields_I) :=
                                      New_Field_Association
                                        (Domain => EW_Term,
                                         Field  => To_Why_Id
                                           (Parent_Comp,
                                            Rec => Parent_With_Eq),
                                         Value  => +Insert_Simple_Conversion
                                           (Expr           => New_Field_Access
                                              (Is_Discr   => False,
                                               Name       => New_Record_Access
                                                 (Name  => +B_Ident,
                                                  Field => Fields_Id),
                                               Field_Id   => Field_Id,
                                               Field_Type =>
                                                 Retysp (Etype (Comp))),
                                            To             => EW_Abstract
                                              (Etype (Parent_Comp)),
                                            Force_No_Slide => True));
                                 end if;
                              end;
                           end loop;
                           pragma Assert (Conj_I = Conjuncts'Last);
                           pragma Assert (Anc_Fields_I = Nb_Anc_Fields);

                           Condition := New_And_Pred (Condition & Conjuncts);
                        end;
                     end if;
                  end;
               end if;

               --  Add the parent user-defined equality if any

               if Present (Parent_With_Eq) then
                  declare
                     Eq_Id : constant W_Identifier_Id :=
                       E_Symb (Parent_With_Eq, WNE_User_Eq);
                     --  We use the user-defined equality on Parent_With_Eq

                  begin
                     Condition := New_And_Pred
                       (Left  => New_Call
                          (Name => Eq_Id,
                           Args =>
                             (1 => New_Ada_Record_Aggregate
                                (Domain       => EW_Term,
                                 Discr_Expr   =>
                                   (if Has_Discriminants (E)
                                    then New_Record_Access
                                      (Name  => +A_Ident,
                                       Field => To_Ident
                                         (WNE_Rec_Split_Discrs))
                                    else Why_Empty),
                                 Field_Assocs => A_Anc_Fields,
                                 Ty           => Parent_With_Eq),
                              2 => New_Ada_Record_Aggregate
                                (Domain       => EW_Term,
                                 Discr_Expr   =>
                                   (if Has_Discriminants (E)
                                    then New_Record_Access
                                      (Name  => +B_Ident,
                                       Field => To_Ident
                                         (WNE_Rec_Split_Discrs))
                                    else Why_Empty),
                                 Field_Assocs => B_Anc_Fields,
                                 Ty           => Parent_With_Eq)),
                           Typ  => EW_Bool_Type),
                        Right => Condition);
                  end;
               end if;

               --  For simple private types, the equality function is the
               --  mathematical equality if we know that it is an appropriate
               --  model of the Ada equality for the full view and
               --  uninterpreted otherwise.

               Emit
                 (Th,
                  New_Function_Decl
                    (Domain      => EW_Pterm,
                     Name        => To_Local (E_Symb (E, WNE_Bool_Eq)),
                     Binders     =>
                       R_Binder &
                       Binder_Array'(1 =>
                                         Binder_Type'(B_Name => B_Ident,
                                                      others => <>)),
                     Return_Type => +EW_Bool_Type,
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Def         =>
                       (if not Is_Simple_Private_Type (E)
                        then New_Conditional
                          (Domain    => EW_Term,
                           Condition => +Condition,
                           Then_Part => +True_Term,
                           Else_Part => +False_Term)

                        --  Give the defintion of the predefined equality on
                        --  hardcoded types. For Big_Reals and Big_Integers it
                        --  should not be necessary as their full view is a
                        --  record type and therefore their primitive equality
                        --  should be used everywhere.

                        elsif Is_Hardcoded_Entity (E)
                        then New_Comparison
                          (Hardcoded_Equality_Symbol (E, EW_Term),
                           +A_Ident, +B_Ident, EW_Term)

                        --  For simple private types, use Why3 "=" if the type
                        --  allows it.

                        elsif Use_Real_Eq_For_Private_Type (E)
                        then New_Comparison
                          (Why_Eq, +A_Ident, +B_Ident, EW_Term)
                        else Why_Empty)));
            end;
         end if;
      end Declare_Equality_Function;

      ----------------------------------
      -- Declare_Extraction_Functions --
      ----------------------------------

      procedure Declare_Extraction_Functions (Components : Node_Lists.List) is
         Root_Ext_Type   : constant W_Type_Id := New_Named_Type
           (Name => Get_Name (E_Symb (Root, WNE_Extension_Type)));
         E_Ext_Type      : constant W_Type_Id := New_Named_Type
           (To_Local (E_Symb (E, WNE_Extension_Type)));
         X_Ident         : constant W_Identifier_Id :=
           New_Identifier (Name => "x", Typ => Root_Ext_Type);
         Binder          : constant Binder_Array :=
           (1 => (B_Name => X_Ident,
                  others => <>));
         Hide_Name       : constant W_Identifier_Id :=
           To_Ident (WNE_Hide_Extension);
         Extract_Func    : constant W_Identifier_Id :=
           Extract_Extension_Fun (E);
         Num_Hide_Params : constant Natural :=
           Natural (Components.Length)
           + 1;  --  for the extension field of the current type
         Hide_Binders    : Binder_Array (1 .. Num_Hide_Params);
         Index           : Natural := 0;

      begin
         for Field of Components loop
            Index := Index + 1;
            Hide_Binders (Index) :=
              (B_Name =>
                 New_Identifier (Name => Full_Name (Field),
                                 Typ  => W_Type_Of_Component
                                   (Field, E, Init_Wrapper => False)),
               others => <>);

            --  function extract__<comp> (x : root.__exp_type) : <typ>

            --  If an extraction function is already present in the base type
            --  or parent type of E, then the extraction function is a renaming
            --  of the base type's extraction function.

            declare
               Has_Definition : constant Boolean :=
                 Original_Declaration (Field) /= E;
               --  Field has a definition if its first declaration is not E

               Definition     : constant W_Expr_Id :=
                 (if Has_Definition then
                     New_Call
                    (Domain   => EW_Term,
                     Name     =>
                       Extract_Fun (Field,
                         Rec   => Original_Declaration (Field),
                         Local => False),
                     Binders  => Binder,
                     Typ      => W_Type_Of_Component
                       (Field, E, Init_Wrapper => False))
                  else Why_Empty);
            begin
               Emit (Th,
                     New_Function_Decl
                       (Domain      => EW_Pterm,
                        Name        => Extract_Fun (Field, Rec => E),
                        Binders     => Binder,
                        Labels      => Symbol_Sets.Empty_Set,
                        Location    => No_Location,
                        Return_Type => W_Type_Of_Component
                          (Field, E, Init_Wrapper => False),
                        Def         => Definition));
            end;
         end loop;

         --  The extension field in the current type is also part of the
         --  extension field in the root type

         Index := Index + 1;
         Hide_Binders (Index) :=
           (B_Name => New_Identifier
              (Domain => EW_Term,
               Name   => To_Local (E_Symb (E, WNE_Rec_Extension)),
               Typ    => E_Ext_Type),
            others => <>);

         pragma Assert (Index = Num_Hide_Params);

         --  function hide__ext__ (comp1 : typ1; .. ; ext : __exp_type)
         --                       : root.__exp_type

         Emit (Th,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => Hide_Name,
                  Binders     => Hide_Binders,
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => Root_Ext_Type));

         --  function extract__ext__ (x : __private) : __private

         Emit (Th,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => Extract_Func,
                  Binders     => Binder,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Return_Type => E_Ext_Type));
      end Declare_Extraction_Functions;

      ------------------------------------------------
      -- Declare_Extraction_Functions_For_Extension --
      ------------------------------------------------

      procedure Declare_Extraction_Functions_For_Extension is
         Comps : Node_Lists.List;
      begin
         for Field of Get_Component_Set (E) loop
            if No (Search_Component_In_Type (Root, Field)) then
               Comps.Append (Field);
            end if;
         end loop;

         Declare_Extraction_Functions (Components  => Comps);
      end Declare_Extraction_Functions_For_Extension;

   --  Start of processing for Declare_Rep_Record_Type

   begin
      --  For types which have a private part, declare a new uninterpreted type
      --  for the private part as well as a new equality function and a dummy
      --  declaration of an object of this type. The equality function will be
      --  the mathematical equality if we know that it is an appropriate model
      --  of the Ada equality for the full view and uninterpreted otherwise.

      if not Is_Simple_Private_Type (E) and then Has_Private_Part (E) then
         declare
            Priv_Name : constant W_Name_Id    :=
              To_Local (E_Symb (E, WNE_Private_Type));
            Priv_Ty   : constant W_Type_Id    :=
              New_Named_Type (Name => Priv_Name);
            A_Ident   : constant W_Identifier_Id :=
              New_Identifier (Name => "a", Typ => Priv_Ty);
            B_Ident   : constant W_Identifier_Id :=
              New_Identifier (Name => "b", Typ => Priv_Ty);
            Binders   : constant Binder_Array :=
              (1 => (B_Name => A_Ident, others => <>),
               2 => (B_Name => B_Ident, others => <>));

         begin
            Emit (Th,
                  New_Type_Decl
                    (Name  => Img (Get_Symb (Priv_Name))));
            Emit
              (Th,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (E_Symb (E, WNE_Private_Eq)),
                  Binders     => Binders,
                  Return_Type => +EW_Bool_Type,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,

                  --  Use Why3 "=" for the private part if the type allows it.
                  --  Theoretically, we should only check the components which
                  --  are actually part of this private part (only new
                  --  components in record extensions, no checks for visible
                  --  discriminants etc), but it is not necessary. Indeed,
                  --  Why3 "=" can never be used for tagged types because of
                  --  the extension part and discriminants are discrete types
                  --  which are always ok for equality.

                  Def         =>
                    (if Use_Real_Eq_For_Private_Type (E)
                     then New_Comparison (Why_Eq, +A_Ident, +B_Ident, EW_Term)
                     else Why_Empty)));

            Emit
              (Th,
               New_Function_Decl
                 (Domain      => EW_Term,
                  Name        => To_Local (E_Symb (E, WNE_Private_Dummy)),
                  Binders     => Binder_Array'(1 .. 0 => <>),
                  Return_Type => Priv_Ty,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set));
         end;
      end if;

      --  Emit an abstract type for the extension part of a tagged type along
      --  with a constant standing for the null extension.

      if Is_Tagged_Type (E) then
         Emit (Th,
               New_Type_Decl
                 (Name  => Img
                    (Get_Symb (To_Local (E_Symb (E, WNE_Extension_Type))))));
         Emit (Th,
               Why.Atree.Builders.New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (E_Symb (E, WNE_Null_Extension)),
                  Binders     => (1 .. 0 => <>),
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => New_Named_Type
                    (To_Local (E_Symb (E, WNE_Extension_Type)))));
      end if;

      Declare_Record_Type
        (Th           => Th,
         E            => E,
         Root         => Root,
         Ty_Name      => Ty_Name,
         Reuse_Discr  => not Is_Root,
         Init_Wrapper => False);

      --  We need to delare conversion functions before the protected access
      --  functions, because the former may be used in the latter

      if not Is_Root then
         pragma Assert (not Is_Simple_Private_Type (E));

         if Is_Tagged_Type (E) then
            Declare_Extraction_Functions_For_Extension;
         end if;

         Declare_Conversion_Functions
           (Th           => Th,
            E            => E,
            Root         => Root,
            Ty_Name      => Ty_Name,
            Init_Wrapper => False);

      else
         --  Declare dummy conversion functions that will be used to convert
         --  other types which use E as a representative type.

         Emit
           (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_To_Base)),
               Binders     => R_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         => +A_Ident));
         Emit
           (Th,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_Of_Base)),
               Binders     => R_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         => +A_Ident));
      end if;

      --  No need to declare protected access functions for simple private
      --  types.

      if not Is_Simple_Private_Type (E) then
         Declare_Protected_Access_Functions
           (Th           => Th,
            E            => E,
            Root         => Root,
            Ty_Name      => Ty_Name,
            Reuse_Discr  => not Is_Root,
            Init_Wrapper => False);
      end if;

      Declare_Equality_Function;
   end Declare_Rep_Record_Type;

   ----------------------------------
   -- Discriminant_Check_Pred_Call --
   ----------------------------------

   function Discriminant_Check_Pred_Call
     (E     : Entity_Id;
      Field : Entity_Id;
      Arg   : W_Identifier_Id)
      return W_Pred_Id is
   begin
      return
        New_Call
          (Name => Discriminant_Check_Pred_Name (E, Field, True),
           Args => (1 => +Arg));
   end Discriminant_Check_Pred_Call;

   ----------------------------------
   -- Discriminant_Check_Pred_Name --
   ----------------------------------

   function Discriminant_Check_Pred_Name
     (E            : Entity_Id;
      Field        : Entity_Id;
      Local        : Boolean;
      Relaxed_Init : Boolean := False)
      return W_Identifier_Id
   is
      Orig : constant Entity_Id := Representative_Component (Field);
      Name : constant String := Full_Name (Orig) & "__pred";
   begin
      return Id : W_Identifier_Id do
         if Local then
            Id := New_Identifier (Name => Name);
         else
            Id := New_Identifier
              (Domain   => EW_Pred,
               Ada_Node => E,
               Module   => E_Module (E),
               Name     => Name);
         end if;

         if Relaxed_Init then
            Id := To_Init_Module (Id);
         end if;
      end return;
   end Discriminant_Check_Pred_Name;

   ---------------------------
   -- Extract_Extension_Fun --
   ---------------------------

   function Extract_Extension_Fun
     (Rec   : Entity_Id;
      Local : Boolean := True) return W_Identifier_Id
   is
   begin
      return New_Identifier
        (Name   => To_String (WNE_Extract_Prefix) &
           To_String (WNE_Rec_Extension_Suffix),
         Domain => EW_Term,
         Module =>
           (if Local then Why_Empty else E_Module (Rec)));
   end Extract_Extension_Fun;

   -----------------
   -- Extract_Fun --
   -----------------

   function Extract_Fun
     (Field : Entity_Id;
      Rec   : Entity_Id;
      Local : Boolean := True)
      return W_Identifier_Id
   is
      Prefix : constant Why_Name_Enum := WNE_Extract_Prefix;
      Orig   : constant Entity_Id := Representative_Component (Field);
   begin
      return New_Identifier
        (Name   => To_String (Prefix) & Full_Name (Orig),
         Domain => EW_Term,
         Module =>
           (if Local then Why_Empty else E_Module (Rec)));
   end Extract_Fun;

   ----------------------------------
   -- Field_Type_For_Discriminants --
   ----------------------------------

   function Field_Type_For_Discriminants (E : Entity_Id) return W_Type_Id is
     (New_Type (Ada_Node   => E,
                Is_Mutable => False,
                Type_Kind  => EW_Abstract,
                Name       =>
                   Get_Name (E_Symb (Root_Retysp (E),
                                     WNE_Rec_Split_Discrs))));

   ---------------------------
   -- Field_Type_For_Fields --
   ---------------------------

   function Field_Type_For_Fields
     (E            : Entity_Id;
      Init_Wrapper : Boolean := False) return W_Type_Id
   is
      Symb : constant W_Identifier_Id :=
        E_Symb (E, WNE_Rec_Split_Fields, Init_Wrapper);
      Name : constant W_Name_Id := Get_Name (Symb);
   begin
      return New_Type (Ada_Node   => E,
                       Is_Mutable => False,
                       Type_Kind  => EW_Abstract,
                       Name       => Name);
   end Field_Type_For_Fields;

   -----------------------------------------
   -- Generate_Associations_From_Ancestor --
   -----------------------------------------

   procedure Generate_Associations_From_Ancestor
     (Ada_Node       : Node_Id := Empty;
      Domain         : EW_Domain;
      Expr           : W_Expr_Id;
      Anc_Ty         : Entity_Id;
      Ty             : Entity_Id;
      Discr_Expr     : out W_Expr_Id;
      Field_Assocs   : out W_Field_Association_Array;
      Missing_Fields : in out Component_Sets.Set)
   is
      Component   : Entity_Id;
      Index       : Natural := 0;
      Assoc       : W_Field_Association_Id;

   begin
      --  Ty's discriminants were already defined in Anc_Ty. Generate
      --  association for them.

      if Has_Discriminants (Ty) then
         Discr_Expr := New_Discriminants_Access
           (Ada_Node => Ada_Node,
            Name     => Expr,
            Ty       => Anc_Ty);
      else
         Discr_Expr := Why_Empty;
      end if;

      for Anc_Comp of Get_Component_Set (Anc_Ty) loop

         Component := Search_Component_In_Type (Ty, Anc_Comp);

         pragma Assert (Present (Component));
         Missing_Fields.Exclude (Component);

         Assoc := New_Field_Association
           (Domain => Domain,
            Field  => To_Why_Id (Component, Rec => Ty),
            Value  => New_Ada_Record_Access
              (Ada_Node => Ada_Node,
               Domain   => (if Domain in EW_Prog | EW_Pterm then EW_Pterm
                            else EW_Term),
               Name     => Expr,
               Field    => Anc_Comp,
               Ty       => Anc_Ty));

         Index := Index + 1;
         Field_Assocs (Index) := Assoc;
      end loop;

      pragma Assert (Index = Field_Assocs'Last);
   end Generate_Associations_From_Ancestor;

   --------------------------------
   -- Get_Compatible_Tags_Module --
   --------------------------------

   function Get_Compatible_Tags_Module (E : Entity_Id) return W_Module_Id is
      Name : constant String := Full_Name (E) & "__Compatible_Tags";
   begin
      return New_Module (File => No_Symbol,
                         Name => Name);
   end Get_Compatible_Tags_Module;

   -----------------------------------
   -- Get_Compatible_Tags_Predicate --
   -----------------------------------

   function Get_Compatible_Tags_Predicate
     (E : Entity_Id) return W_Identifier_Id
   is
      M : constant W_Module_Id := Get_Compatible_Tags_Module (Root_Retysp (E));

   begin
      --  For concurrent type, we do not generate any compatibility module.
      --  Raise Program_Error as the frontend seem to handle membership tests
      --  on concurrent types badly. We could simply use
      --  M_Compat_Tags.Compat_Tags_Id instead.

      if Is_Concurrent_Type (E) then
         raise Program_Error;
      else
         return
           New_Identifier (Domain => EW_Pred,
                           Module => M,
                           Symb   => NID ("__compatible_tags"),
                           Typ    => EW_Bool_Type);
      end if;
   end Get_Compatible_Tags_Predicate;

   ----------------------------------
   -- Get_Discriminants_Of_Subtype --
   ----------------------------------

   function Get_Discriminants_Of_Subtype (Ty : Entity_Id) return W_Expr_Array
   is
      Num_Discr : constant Natural := Count_Discriminants (Ty);
      Args      : W_Expr_Array (1 .. Num_Discr);
      Count     : Natural := 1;
      Discr     : Entity_Id := First_Discriminant (Ty);
      Elmt      : Elmt_Id := First_Elmt (Discriminant_Constraint (Ty));

   begin
      while Present (Discr) loop
         Args (Count) :=
           Transform_Expr
             (Domain        => EW_Term,
              Params        => Logic_Params,
              Expr          => Node (Elmt),
              Expected_Type => Base_Why_Type (Etype (Discr)));
         Count := Count + 1;
         Next_Elmt (Elmt);
         Next_Discriminant (Discr);
      end loop;

      return Args;
   end Get_Discriminants_Of_Subtype;

   -------------------------------
   -- Get_Rep_Record_Completion --
   -------------------------------

   function Get_Rep_Record_Completion (E : Entity_Id) return W_Module_Id is
      Ancestor : constant Entity_Id := Oldest_Parent_With_Same_Fields (E);
   begin
      return E_Record_Compl_Module (Ancestor);
   end Get_Rep_Record_Completion;

   ---------------------------
   -- Get_Rep_Record_Module --
   ---------------------------

   function Get_Rep_Record_Module (E : Entity_Id) return W_Module_Id is
      Ancestor : constant Entity_Id := Oldest_Parent_With_Same_Fields (E);
   begin
      return E_Record_Rep_Module (Ancestor);
   end Get_Rep_Record_Module;

   ---------------------
   -- Hidden_Ext_Name --
   ---------------------

   function Hidden_Ext_Name
     (Rec   : Entity_Id;
      Local : Boolean := True) return W_Identifier_Id
   is (New_Identifier
       (Domain => EW_Term,
        Symb   => NID (To_String (WNE_Hidden_Extension)),
        Module => (if Local then Why_Empty
                   else Get_Rep_Record_Completion (Rec)),
        Typ    => EW_Private_Type));

   ---------------------------
   -- Hidden_Component_Name --
   ---------------------------

   function Hidden_Component_Name
     (Field : Entity_Id;
      Rec   : Entity_Id;
      Local : Boolean := True) return W_Identifier_Id
   is
      Orig : constant Entity_Id := Representative_Component (Field);
      Name : constant String :=
        To_String (WNE_Rec_Comp_Prefix) & (Full_Name (Orig)) & "__"
        & To_String (WNE_Rec_Extension_Suffix);
      pragma Assert (Field /= Rec);
      Typ  : constant W_Type_Id :=
        W_Type_Of_Component (Field        => Field,
                             Rec          => Rec,
                             Init_Wrapper => False);
   begin
      return New_Identifier
       (Domain => EW_Term,
        Symb   => NID (Name),
        Module => (if Local then Why_Empty
                   else Get_Rep_Record_Completion (Rec)),
        Typ    => Typ);
   end Hidden_Component_Name;

   ---------------------------------------
   -- Insert_Subtype_Discriminant_Check --
   ---------------------------------------

   function Insert_Subtype_Discriminant_Check
     (Ada_Node : Node_Id;
      Check_Ty : Entity_Id;
      Expr     : W_Prog_Id)
      return W_Prog_Id
   is
      Root     : constant Entity_Id := Root_Retysp (Check_Ty);
      Tmp_Expr : constant W_Expr_Id := New_Temp_For_Expr (+Expr);
   begin
      return
        +Binding_For_Temp
        (Ada_Node => Ada_Node,
         Domain   => EW_Prog,
         Tmp      => Tmp_Expr,
         Context  => +Sequence
           (Ada_Node => Ada_Node,
            Left     => New_VC_Call
              (Ada_Node => Ada_Node,
               Name     => Range_Check_Name (Root, RCK_Range),
               Progs    => Prepare_Args_For_Subtype_Check
                 (Check_Ty, Tmp_Expr),
               Reason   => VC_Discriminant_Check,
               Typ      => EW_Unit_Type),
            Right    => +Tmp_Expr));
   end Insert_Subtype_Discriminant_Check;

   ----------------------
   -- Insert_Tag_Check --
   ----------------------

   function Insert_Tag_Check
     (Ada_Node : Node_Id;
      Check_Ty : Entity_Id;
      Expr     : W_Prog_Id)
      return W_Prog_Id
   is
      Root  : constant Entity_Id := Root_Retysp (Check_Ty);
      Id    : constant W_Expr_Id := New_Temp_For_Expr (+Expr);
      Call  : constant W_Expr_Id := New_Call
        (Ada_Node => Ada_Node,
         Domain   => EW_Pred,
         Name     => Get_Compatible_Tags_Predicate (Root),
         Args     =>
           (1 => New_Tag_Access
                (Domain => EW_Term,
                 Name   => Insert_Simple_Conversion
                   (Ada_Node => Ada_Node,
                    Domain   => EW_Term,
                    Expr     => Id,
                    To       => EW_Abstract
                      (Root,
                       Relaxed_Init => Get_Relaxed_Init (Get_Type (Id)))),
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
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Field    : Entity_Id;
      Ty       : Entity_Id)
      return W_Expr_Id
   is
      Rec          : constant Entity_Id :=
        (if Ekind (Field) /= E_Discriminant then Ty
         else Root_Retysp (Ty));
      Init_Wrapper : constant Boolean :=
        Get_Relaxed_Init (Get_Type (+Name));
      --  Use the init wrapper type if needed

      Call_Id      : constant W_Identifier_Id :=
        To_Why_Id
          (Field,
           Rec          => Rec,
           Relaxed_Init => Init_Wrapper
           and then Ekind (Field) /= E_Discriminant);

      Ret_Ty       : constant W_Type_Id :=
        (if Is_Part_Of_Protected_Object (Field) then
              EW_Abstract (Etype (Field))
         elsif Is_Type (Field) then
              New_Named_Type (Name         => Get_Name
                              (E_Symb (E            => Field,
                                       S            => WNE_Private_Type,
                                       Relaxed_Init => Init_Wrapper)),
                              Relaxed_Init => Init_Wrapper)
         else W_Type_Of_Component
           (Search_Component_In_Type (Ty, Field), Empty,
            Init_Wrapper => Init_Wrapper));
      Top_Field    : constant W_Expr_Id :=
        (if Ekind (Field) = E_Discriminant
         then New_Discriminants_Access (Ada_Node, Name, Ty)
         else New_Fields_Access (Ada_Node, Name, Ty));
   begin
      if Domain = EW_Prog
        and then Ekind (Field) = E_Component
        and then Retysp_Kind (Rec) in Incomplete_Or_Private_Kind | Record_Kind
        and then Has_Variant_Info (Rec, Field)
      then
         return
           +New_VC_Call
             (Ada_Node => Ada_Node,
              Name     => To_Program_Space (Call_Id),
              Progs    => (1 => Name),
              Reason   => VC_Discriminant_Check,
              Typ      => Ret_Ty);

      else
         return
           New_Record_Access
             (Ada_Node => Ada_Node,
              Field    => Call_Id,
              Name     => Top_Field,
              Typ      => Ret_Ty);
      end if;
   end New_Ada_Record_Access;

   ------------------------------
   -- New_Ada_Record_Aggregate --
   ------------------------------

   function New_Ada_Record_Aggregate
     (Ada_Node       : Node_Id := Empty;
      Domain         : EW_Domain;
      Discr_Expr     : W_Expr_Id;
      Field_Assocs   : W_Field_Association_Array;
      Ty             : Entity_Id;
      Init_Wrapper   : Boolean := False;
      Missing_Fields : Component_Sets.Set := Component_Sets.Empty_Set)
      return W_Expr_Id
   is
      Num_All    : constant Natural := Count_Why_Top_Level_Fields (Ty);
      Num_Discr  : constant Natural := Count_Discriminants (Ty);
      Num_Fields : constant Natural := Count_Why_Regular_Fields (Ty);
      Assoc      : W_Field_Association_Id;
      Assocs     : W_Field_Association_Array (1 .. Num_All);
      Index      : Natural := 0;
      Result     : W_Expr_Id;

   begin
      if Num_Discr > 0 then
         Assoc := New_Field_Association
           (Domain   => Domain,
            Field    => E_Symb (Ty, WNE_Rec_Split_Discrs, Init_Wrapper),
            Value    => Discr_Expr);
         Index := Index + 1;
         Assocs (Index) := Assoc;
      end if;

      if Num_Fields > 0 then
         declare
            All_Field_Assocs : W_Field_Association_Array (1 .. Num_Fields);
            Index            : Natural := Field_Assocs'Length;

         begin
            --  Copy fields from aggregate

            All_Field_Assocs (1 .. Index) := Field_Assocs;

            --  Insert dummy values for the fields that are not in the
            --  aggregate.

            for Comp of Missing_Fields loop
               pragma Assert (not Is_Type (Comp));

               Index := Index + 1;
               All_Field_Assocs (Index) :=
                 New_Field_Association
                   (Domain => Domain,
                    Field  =>
                      To_Why_Id
                        (Comp, Rec => Ty, Relaxed_Init => Init_Wrapper),
                    Value  =>
                      (if Init_Wrapper
                       or else SPARK_Definition.Has_Relaxed_Init
                         (Etype (Comp))
                       then Insert_Simple_Conversion
                         (Ada_Node       => Empty,
                          Domain         => Domain,
                          Expr           => Why_Default_Value
                            (EW_Term, Etype (Comp)),
                          To             => EW_Abstract
                            (Etype (Comp), Relaxed_Init => True),
                          Force_No_Slide => True)
                       else Why_Default_Value (EW_Term, Etype (Comp))));
            end loop;

            if Is_Tagged_Type (Ty) then
               Index := Index + 1;
               All_Field_Assocs (Index) :=
                 New_Field_Association
                   (Domain => Domain,
                    Field  => E_Symb (Ty, WNE_Rec_Extension),
                    Value  => +E_Symb (Ty, WNE_Null_Extension));
            end if;

            pragma Assert (Index = Num_Fields);

            Assoc := New_Field_Association
              (Domain => Domain,
               Field  => E_Symb (Ty, WNE_Rec_Split_Fields, Init_Wrapper),
               Value  => New_Record_Aggregate
                 (Ada_Node     => Ada_Node,
                  Associations => All_Field_Assocs));
         end;
         Index := Index + 1;
         Assocs (Index) := Assoc;
      end if;

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
         Typ          => EW_Abstract (Ty, Relaxed_Init => Init_Wrapper));

      --  If the target type has a direct or inherited predicate, generate a
      --  corresponding check.

      if Domain = EW_Prog
        and then Has_Predicates (Ty)
      then
         Result := +Insert_Predicate_Check
           (Ada_Node => Ada_Node,
            Check_Ty => Ty,
            W_Expr   => +Result);
      end if;

      return Result;
   end New_Ada_Record_Aggregate;

   function New_Ada_Record_Aggregate
     (Ada_Node       : Node_Id := Empty;
      Domain         : EW_Domain;
      Discr_Assocs   : W_Field_Association_Array;
      Field_Assocs   : W_Field_Association_Array;
      Ty             : Entity_Id;
      Init_Wrapper   : Boolean := False;
      Missing_Fields : Component_Sets.Set := Component_Sets.Empty_Set)
      return W_Expr_Id
   is
      Discr_Expr : constant W_Expr_Id :=
        (if Has_Discriminants (Ty)
         then New_Record_Aggregate (Associations => Discr_Assocs)
         else Why_Empty);

   begin
      return New_Ada_Record_Aggregate
        (Ada_Node, Domain, Discr_Expr, Field_Assocs, Ty, Init_Wrapper,
         Missing_Fields);
   end New_Ada_Record_Aggregate;

   ------------------------------------
   -- New_Ada_Record_Check_For_Field --
   ------------------------------------

   function New_Ada_Record_Check_For_Field
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Field    : Entity_Id;
      Ty       : Entity_Id)
      return W_Expr_Id
   is
      Init_Wrapper : constant Boolean := Get_Relaxed_Init (Get_Type (+Name));
      --  Use the init wrapper type if needed
   begin
      --  Do not emit checks for part of variables or discriminants

      if Ekind (Field) = E_Component then
         declare
            Pred_Name : constant W_Identifier_Id :=
              Discriminant_Check_Pred_Name
                (Ty, Field, Local => False, Relaxed_Init => Init_Wrapper);
         begin
            return
              New_Call
                (Ada_Node => Ada_Node,
                 Name     => Pred_Name,
                 Args     => (1 => Name),
                 Domain   => Domain,
                 Typ      => EW_Bool_Type);
         end;
      else
         return New_Literal (Domain => Domain,
                             Value  => EW_True);
      end if;
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
      Tmp       : constant W_Expr_Id := New_Temp_For_Expr (Name);
      Ty        : constant Entity_Id := Get_Ada_Node (+Get_Type (Name));
      Top_Field : constant W_Expr_Id := New_Fields_Access (Ada_Node, Tmp, Ty);

      Init_Wrapper : constant Boolean :=
        Is_Init_Wrapper_Type (Get_Type (Name));
      Field_Name   : constant W_Identifier_Id :=
        To_Why_Id (Field, Domain, Rec => Ty, Relaxed_Init => Init_Wrapper);

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
                      Field  => Field_Name,
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
      Tmp       : constant W_Expr_Id := New_Temp_For_Expr (Name);
      Ty        : constant Entity_Id := Get_Ada_Node (+Get_Type (Name));
      Top_Field : constant W_Expr_Id := New_Fields_Access (Ada_Node, Tmp, Ty);

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
      Name     : W_Expr_Id;
      Ty       : Entity_Id)
      return W_Expr_Id
   is
      Init_Wrapper : constant Boolean := Get_Relaxed_Init (Get_Type (+Name));
      --  Use the init wrapper type if needed
   begin
      return New_Record_Access
        (Ada_Node => Ada_Node,
         Field    => E_Symb (Ty, WNE_Rec_Split_Discrs, Init_Wrapper),
         Name     => Name);
   end New_Discriminants_Access;

   -----------------------
   -- New_Fields_Access --
   -----------------------

   function New_Fields_Access
     (Ada_Node : Node_Id := Empty;
      Name     : W_Expr_Id;
      Ty       : Entity_Id)
      return W_Expr_Id
   is
      Init_Wrapper : constant Boolean := Get_Relaxed_Init (Get_Type (+Name));
      --  Use the init wrapper type if needed
   begin
      return New_Record_Access
        (Ada_Node => Ada_Node,
         Field    => E_Symb (Ty, WNE_Rec_Split_Fields, Init_Wrapper),
         Name     => Name);
   end New_Fields_Access;

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
      Init_Wrapper : constant Boolean := Get_Relaxed_Init (Get_Type (+Name));
      --  Use the init wrapper type if needed
   begin
      return New_Record_Update
        (Ada_Node => Ada_Node,
         Name     => Name,
         Updates  =>
           (1 => New_Field_Association
                (Domain => Domain,
                 Field  => E_Symb (Ty, WNE_Rec_Split_Fields, Init_Wrapper),
                 Value  => Value)),
         Typ      => Get_Type (+Name));
   end New_Fields_Update;

   --------------------------------
   -- New_Record_Is_Moved_Access --
   --------------------------------

   function New_Record_Is_Moved_Access
     (E    : Entity_Id;
      Name : W_Expr_Id)
      return W_Expr_Id
   is
      Init_Wrapper : constant Boolean := Get_Relaxed_Init (Get_Type (+Name));
      --  Use the init wrapper type if needed
   begin
      return New_Record_Access
        (Name  => +Name,
         Field => E_Symb (E, WNE_Is_Moved_Field, Init_Wrapper),
         Typ   => EW_Bool_Type);
   end New_Record_Is_Moved_Access;

   --------------------------------
   -- New_Record_Is_Moved_Update --
   --------------------------------

   function New_Record_Is_Moved_Update
     (E     : Entity_Id;
      Name  : W_Prog_Id;
      Value : W_Prog_Id)
      return W_Prog_Id
   is
      Init_Wrapper : constant Boolean := Get_Relaxed_Init (Get_Type (+Name));
      --  Use the init wrapper type if needed
   begin
      return New_Record_Update
        (Name    => Name,
         Updates =>
           (1 => New_Field_Association
                (Domain => EW_Prog,
                 Field  => E_Symb (E, WNE_Is_Moved_Field, Init_Wrapper),
                 Value  => +Value)),
         Typ     => Get_Type (+Name));
   end New_Record_Is_Moved_Update;

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

   --------------------
   -- New_Tag_Update --
   --------------------

   function New_Tag_Update
     (Ada_Node  : Node_Id := Empty;
      Domain    : EW_Domain;
      Name      : W_Expr_Id;
      From_Expr : W_Expr_Id := Why_Empty;
      Ty        : Entity_Id)
      return W_Expr_Id
   is
      Has_Tag : constant Boolean :=
        (Is_Tagged_Type (Retysp (Ty))
         and then (From_Expr /= Why_Empty
           or else not Is_Class_Wide_Type (Ty)));
      --  If Ty is tagged, its 'Tag attribute should be preserved except for
      --  defaults of classwide types.

   begin
      if Has_Tag then
         declare
            Value : constant W_Expr_Id :=
              (if From_Expr = Why_Empty then
                  +E_Symb (E => Ty, S => WNE_Tag)
               else New_Tag_Access
                 (Domain => Domain,
                  Name   => From_Expr,
                  Ty     => Get_Ada_Node (+Get_Type (From_Expr))));
         begin
            return
              (New_Record_Update
                 (Ada_Node => Ada_Node,
                  Name     => Name,
                  Updates  =>
                    (1 => New_Field_Association
                         (Domain => Domain,
                          Field  => +New_Attribute_Expr
                            (Ty     => Ty,
                             Domain => Domain,
                             Attr   => Attribute_Tag),
                          Value  => Value)),
                  Typ      => Get_Type (Name)));
         end;
      else
         return Name;
      end if;
   end New_Tag_Update;

   ------------------------------------
   -- Oldest_Parent_With_Same_Fields --
   ------------------------------------

   function Oldest_Parent_With_Same_Fields (E : Entity_Id) return Entity_Id is
      Current  : Entity_Id := Retysp (E);
      Ancestor : Entity_Id := Current;

   begin
      --  Concurrent types are not handled

      if Is_Concurrent_Type (Current) then
         return E;
      end if;

      --  If E has discriminants and components whose type depends on this
      --  discriminant, it has no older parent with the same fields.
      --  To check if the type of a component depends on a discriminant, we
      --  search for components which do not have the same type as their
      --  first introduction.

      if Has_Discriminants (Current) then
         for Field of Get_Component_Set (Current) loop
            if Ekind (Field) = E_Component
              and then Retysp (Etype (Representative_Component (Field)))
              /= Retysp (Etype (Field))
            then
               return Current;
            end if;
         end loop;
      end if;

      --  If E is not tagged then the root type has the same fields as E

      if not Is_Tagged_Type (Current) then
         return Root_Retysp (Current);

      else
         --  Otherwise, we follow the Etype link until we find a type with
         --  more fields.

         loop
            --  If Current is private, its fullview is not in SPARK. Thus, it
            --  is considered to have private fields of its own.

            if Has_Private_Part (Current) then
               return Current;
            end if;

            --  Use the Etype field or the first ancestor in SPARK to get to
            --  parent type.
            --  Note that, even if Current is not a private type, its full
            --  view may still not be in SPARK, in particular when it is
            --  a (non-private) tagged derivation of a private type.

            Ancestor := Retysp (Etype (Current));

            --  At this point we have reached as high as we could in the
            --  hierarchy (or derived types and subtypes) while staying in
            --  SPARK.

            if Ancestor = Current then
               return Current;
            end if;

            --  If Current is not subtype, check whether it has more fields
            --  than Ancestor.

            if Is_Base_Type (Current) then
               for Field of Get_Component_Set (Current) loop

                  --  If Field is not in Ancestor, we are done.

                  if No (Search_Component_In_Type (Ancestor, Field)) then
                     return Current;
                  end if;
               end loop;
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
      Expr     : W_Expr_Id)
      return W_Expr_Array
   is
     (Get_Discriminants_Of_Subtype (Check_Ty)
      & New_Discriminants_Access
        (Name => Expr,
         Ty   => Get_Ada_Node (+Get_Type (Expr))));

   ----------------------------
   -- Record_From_Split_Form --
   ----------------------------

   function Record_From_Split_Form
     (Ada_Node     : Node_Id := Empty;
      A            : W_Expr_Array;
      Ty           : Entity_Id;
      Init_Wrapper : Boolean := False)
      return W_Term_Id
   is
      Associations : W_Field_Association_Array (A'Range);
      Index        : Positive := A'First;

   begin
      --  Store association for the top-level field for fields

      if Count_Why_Regular_Fields (Ty) > 0 then
         Associations (Index) := New_Field_Association
           (Domain   => EW_Term,
            Field    => E_Symb (Ty, WNE_Rec_Split_Fields, Init_Wrapper),
            Value    => A (Index));
         Index := Index + 1;
      end if;

      --  Store association for the top-level field for discriminants

      if Has_Discriminants (Ty) then
         Associations (Index) := New_Field_Association
           (Domain   => EW_Term,
            Field    => E_Symb (Ty, WNE_Rec_Split_Discrs, Init_Wrapper),
            Value    => A (Index));
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

      --  Store association for the is_moved flag

      if Has_Ownership_Annotation (Ty) and then Needs_Reclamation (Ty) then
         Associations (Index) := New_Field_Association
           (Domain => EW_Term,
            Field  => E_Symb (Ty, WNE_Is_Moved_Field, Init_Wrapper),
            Value  => A (Index));
         Index := Index + 1;
      end if;

      return New_Record_Aggregate
        (Ada_Node     => Ada_Node,
         Associations => Associations,
         Typ          => EW_Abstract (Ty, Relaxed_Init => Init_Wrapper));
   end Record_From_Split_Form;

   function Record_From_Split_Form
     (I           : Item_Type;
      Ref_Allowed : Boolean)
      return W_Term_Id
   is
      E            : constant Entity_Id :=
        (if I.Fields.Present then I.Fields.Binder.Ada_Node
         else I.Discrs.Binder.Ada_Node);
      Relaxed_Init : constant Boolean :=
        (if I.Fields.Present and Has_Init_Wrapper (I.Typ)
         then Get_Module (Get_Name (Get_Typ (I.Fields.Binder.B_Name)))
         = E_Init_Module (I.Typ)
         else False);
      Ty           : constant Entity_Id := I.Typ;
      Values       : W_Expr_Array (1 .. Count_Why_Top_Level_Fields (Ty));
      Index        : Positive := 1;

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

      --  Store association for the 'Tag attribute

      if I.Tag.Present then
         Values (Index) := +I.Tag.Id;
         Index := Index + 1;
      end if;

      --  Store association for the Is_Moved flag

      if I.Is_Moved_R.Present then
         if Ref_Allowed then
            Values (Index) := New_Deref (E, +I.Is_Moved_R.Id, EW_Bool_Type);
         else
            Values (Index) := +I.Is_Moved_R.Id;
         end if;
         Index := Index + 1;
      end if;

      pragma Assert (Index = Values'Last + 1);

      return Record_From_Split_Form (E, Values, Ty, Relaxed_Init);
   end Record_From_Split_Form;

   --------------------------------
   -- Record_Type_Cloned_Subtype --
   --------------------------------

   function Record_Type_Cloned_Subtype (E : Entity_Id) return Entity_Id is
      Result : Entity_Id := E;
   begin
      while Record_Type_Is_Clone (Result) loop

         --  Classwide types are translated as clones of their specific types

         if Is_Class_Wide_Type (Result) then
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

         --  Result is not a cloned record type

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

      if Is_Class_Wide_Type (E) then
         return True;

      --  Empty record types are not clones

      elsif Count_Why_Top_Level_Fields (E) = 0 then
         return False;

      --  Subtypes with a cloned_subtype are clones

      elsif Ekind (E) = E_Record_Subtype
        and then Present (Cloned_Subtype (E))
        and then Is_Constrained (Cloned_Subtype (E)) = Is_Constrained (E)
      then
         return True;

      --  Untagged private subtypes with no discriminants are clones

      elsif Ekind (E) = E_Private_Subtype
        and then not Is_Tagged_Type (E)
        and then not Has_Discriminants (E)
      then
         return True;

      --  The default is that we don't consider a type as a clone

      else
         return False;
      end if;
   end Record_Type_Is_Clone;

   ------------------------
   -- Tag_Representation --
   ------------------------

   package body Tag_Representation is

      -------------
      -- Get_Tag --
      -------------

      function Get_Tag (Ty : Type_Kind_Id) return Int is
         Position : Node_To_Int_Maps.Cursor;
         Inserted : Boolean;
      begin
         Used_Tags.Insert (Ty, Last_Tag_Used + 1, Position, Inserted);
         if Inserted then
            Last_Tag_Used := Last_Tag_Used + 1;
         end if;
         return Node_To_Int_Maps.Element (Position);
      end Get_Tag;

   end Tag_Representation;

end Why.Gen.Records;
