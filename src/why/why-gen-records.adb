------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - R E C O R D S                       --
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

with Common_Containers;    use Common_Containers;
with Elists;               use Elists;
with GNAT.Source_Info;
with GNATCOLL.Symbols;     use GNATCOLL.Symbols;
with Gnat2Why.Expr;        use Gnat2Why.Expr;
with Gnat2Why.Tables;      use Gnat2Why.Tables;
with Namet;                use Namet;
with Nlists;               use Nlists;
with Sinput;               use Sinput;
with Snames;               use Snames;
with SPARK_Util;           use SPARK_Util;
with SPARK_Util.Hardcoded; use SPARK_Util.Hardcoded;
with SPARK_Util.Types;     use SPARK_Util.Types;
with Uintp;                use Uintp;
with VC_Kinds;             use VC_Kinds;
with Why.Atree.Accessors;  use Why.Atree.Accessors;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Atree.Modules;    use Why.Atree.Modules;
with Why.Conversions;      use Why.Conversions;
with Why.Gen.Decl;         use Why.Gen.Decl;
with Why.Gen.Expr;         use Why.Gen.Expr;
with Why.Gen.Hardcoded;    use Why.Gen.Hardcoded;
with Why.Gen.Init;         use Why.Gen.Init;
with Why.Gen.Names;        use Why.Gen.Names;
with Why.Gen.Preds;        use Why.Gen.Preds;
with Why.Gen.Progs;        use Why.Gen.Progs;
with Why.Gen.Terms;        use Why.Gen.Terms;
with Why.Images;           use Why.Images;
with Why.Inter;            use Why.Inter;

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

   function Count_Fields_Not_In_Root (E : Entity_Id) return Natural;
   --  Counts the number of fields for the Why3 record representing type E that
   --  are not present in the representation of the root type for E.

   function Get_Rep_Record_Module (E : Entity_Id) return W_Module_Id;
   --  Return the name of a record's representative module.

   procedure Declare_Rep_Record_Type
     (P : W_Section_Id;
      E : Entity_Id);
   --  Emit all necessary Why3 declarations to support Ada records. This also
   --  supports variant records, private types and concurrent types.
   --  @param P the Why section to insert the declaration
   --  @param E the type entity to translate

   procedure Declare_Conversion_Check_Function
     (Section : W_Section_Id;
      Root    : Entity_Id);
   --  generate the program function which is used to insert subtype
   --  discriminant checks

   procedure Declare_Attributes
     (P : W_Section_Id;
      E : Entity_Id);
   --  Declare functions for the record attributes

   procedure Declare_Component_Attributes
     (P : W_Section_Id;
      E : Entity_Id);
   --  Declare functions for the component attributes

   function Discriminant_Check_Pred_Name
     (E     : Entity_Id;
      Field : Entity_Id;
      Local : Boolean)
      return W_Identifier_Id;
   --  Given a record field, return the name of its discrimant check
   --  predicate. If Local is true, do not prefix the identifier.
   --  If the current record type is not a root type, return the name of the
   --  corresponding predicate in the root type module.

   function W_Type_Of_Component
     (Field : Entity_Id;
      Rec   : Entity_Id) return W_Type_Id
   is (if Field = Rec then
           New_Named_Type
             (Name => Get_Name (To_Local (E_Symb (Rec, WNE_Private_Type))))
       elsif Is_Type (Field) then
           New_Named_Type
             (Name => Get_Name (E_Symb (Field, WNE_Private_Type)))
       elsif Ekind (Field) = E_Discriminant then EW_Abstract (Etype (Field))
       else EW_Init_Wrapper (Etype (Field), EW_Abstract));
   --  Compute the expected Why type of a record component. If the component is
   --  a type, it stands for the invisible fields of the type and is translated
   --  as the appropriate private type. Otherwise, return the abstract type of
   --  the component.
   --  @param Field component whose type we are interested in
   --  @param Rec record type we are currently defining if any

   --------------------------------
   -- Build_Predicate_For_Record --
   --------------------------------

   function Build_Predicate_For_Record
     (Expr : W_Term_Id; Ty : Entity_Id) return W_Pred_Id is

      C_Ty    : constant Entity_Id :=
        (if Is_Class_Wide_Type (Ty) then Get_Specific_Type_From_Classwide (Ty)
         else Ty);
      Ty_Ext  : constant Entity_Id := Retysp (C_Ty);
      R_Expr  : constant W_Expr_Id :=
        Insert_Simple_Conversion (Domain   => EW_Term,
                                  Expr     => +Expr,
                                  To       => EW_Abstract (Ty_Ext));
      Discrs  : constant Natural := Count_Discriminants (Ty_Ext);
      Discr   : Node_Id := (if Has_Discriminants (Ty_Ext)
                            then First_Discriminant (Ty_Ext)
                            else Empty);
      T_Comp  : W_Pred_Id;
      T_Guard : W_Pred_Id;
      R_Acc   : W_Expr_Id;
      Tmps    : W_Identifier_Array (1 .. Discrs);
      Binds   : W_Expr_Array (1 .. Discrs);
      I       : Positive := 1;
      T       : W_Pred_Id := True_Pred;

   begin
      --  As discriminants may occur in bounds of types of other fields,
      --  store them in the Symbol_Table.

      Ada_Ent_To_Why.Push_Scope (Symbol_Table);

      while Present (Discr) loop
            R_Acc := New_Ada_Record_Access
              (Empty, EW_Term, R_Expr, Discr, Ty_Ext);

            Tmps (I) := New_Temp_Identifier
              (Discr, EW_Abstract (Etype (Discr)));
            Binds (I) := R_Acc;

            --  We need entities of discrimiants

            Insert_Entity (Discr, Tmps (I));

            --  Call Build_Predicate_For_Discr on discriminants

            T_Comp :=
              Build_Predicate_For_Discr
                (D_Expr => +R_Acc,
                 D_Ty   => Etype (Discr),
                 E      => Discr);

            T := +New_And_Then_Expr (Left   => +T,
                                     Right  => +T_Comp,
                                     Domain => EW_Pred);

         Next_Discriminant (Discr);
         I := I + 1;
      end loop;

      declare
         Fields    : Node_Sets.Set renames Get_Component_Set (Ty_Ext);
         Conjuncts : W_Expr_Array (1 .. Natural (Fields.Length));
         Count     : Natural := 0;
      begin
         for Field of Fields loop

            --  Only consider components and part of variables

            if not Is_Type (Field) then
               pragma Assert (Ekind (Field) /= E_Discriminant);

               R_Acc := New_Ada_Record_Access
                 (Empty, EW_Term, R_Expr, Field, Ty_Ext);

               --  Call Build_Predicate_For_Field on fields

               T_Comp :=
                 Build_Predicate_For_Field
                   (F_Expr => +R_Acc,
                    F_Ty   => Etype (Field),
                    E      => Field);

               if T_Comp /= True_Pred then
                  T_Guard := +New_Ada_Record_Check_For_Field
                    (Empty, EW_Pred, R_Expr, Field, Ty_Ext);

                  Count := Count + 1;
                  Conjuncts (Count) := New_Conditional (Domain    => EW_Pred,
                                                        Condition => +T_Guard,
                                                        Then_Part => +T_Comp);
               end if;
            end if;
         end loop;

         if Count > 0 then
            T := +New_And_Then_Expr
              (+T,
               New_And_Expr (Conjuncts (1 .. Count), EW_Pred),
               EW_Pred);
         end if;
      end;

      if T /= True_Pred then
         for I in 1 .. Discrs loop
            T := +New_Typed_Binding
              (Domain  => EW_Pred,
               Name    => Tmps (I),
               Def     => Binds (I),
               Context => +T);
         end loop;
      end if;

      Ada_Ent_To_Why.Pop_Scope (Symbol_Table);

      return T;
   end Build_Predicate_For_Record;

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

   ----------------------------------------
   -- Create_Rep_Record_Theory_If_Needed --
   ----------------------------------------

   procedure Create_Rep_Record_Theory_If_Needed
     (P : W_Section_Id;
      E : Entity_Id)
   is
      Ancestor : constant Entity_Id := Oldest_Parent_With_Same_Fields (E);
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

      Close_Theory (P, Kind => Definition_Theory, Defined_Entity => E);
   end Create_Rep_Record_Theory_If_Needed;

   ------------------------
   -- Declare_Ada_Record --
   ------------------------

   procedure Declare_Ada_Record
     (P : W_Section_Id;
      E : Entity_Id)
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
            Emit (P,
                  New_Type_Decl
                    (Name   => Ty_Name,
                     Labels => Symbol_Sets.Empty_Set));
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
                 (Domain      => EW_Pterm,
                  Name        => To_Local (E_Symb (E, WNE_To_Base)),
                  Binders     => R_Binder,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Return_Type => (if Is_Root then Abstr_Ty
                                  else EW_Abstract (Root)),
                  Def         => +A_Ident));
            Emit
              (P,
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
              (P,
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

            Emit
              (P,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => New_Identifier (Name => "user_eq"),
                  Return_Type => EW_Bool_Type,
                  Binders     => R_Binder &
                    Binder_Array'(1 => Binder_Type'(B_Name => B_Ident,
                                                    others => <>)),
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set));
         end;

         Declare_Attributes (P, E);

         return;
      end if;

      if Record_Type_Is_Clone (E) then

         --  This type is simply a copy of an existing type, we re-export the
         --  corresponding module and then return.

         declare
            Clone : constant Entity_Id := Record_Type_Cloned_Subtype (E);
         begin
            Add_With_Clause (P, E_Module (Clone), EW_Export);

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
                 (Domain      => EW_Pterm,
                  Name        => To_Local (E_Symb (E, WNE_Tag)),
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => EW_Int_Type));
      end if;

      if Root = E
        and then Has_Discriminants (E)
        and then not Is_Constrained (E)
      then
         Declare_Conversion_Check_Function (P, Root);
      end if;

      Declare_Attributes (P, E);
      Declare_Component_Attributes (P, E);

      --  Declare place-holder for primitive equality function

      declare
         B_Ident : constant W_Identifier_Id :=
           New_Identifier (Name => "b", Typ => Abstr_Ty);
      begin
         Emit
           (P,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => New_Identifier (Name => "user_eq"),
               Return_Type => EW_Bool_Type,
               Binders     => R_Binder &
                 Binder_Array'(1 => Binder_Type'(B_Name => B_Ident,
                                                 others => <>)),
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set));
      end;

   end Declare_Ada_Record;

   ------------------------
   -- Declare_Attributes --
   ------------------------

   procedure Declare_Attributes
     (P : W_Section_Id;
      E : Entity_Id)
   is
   begin
      --  The value size is defined as a logic constant

      Emit (P,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_Attr_Value_Size)),
               Labels      => Symbol_Sets.Empty_Set,
               Location    => No_Location,
               Return_Type => EW_Int_Type));

      --  The object size is defined as a logic constant

      Emit (P,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_Attr_Object_Size)),
               Labels      => Symbol_Sets.Empty_Set,
               Location    => No_Location,
               Return_Type => EW_Int_Type));

      --  The alignement is defined as a logic constant

      Emit (P,
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
                          Name     => NID ("alignment_axiom"),
                          Def      => Alignment_Axiom));
      end;
   end Declare_Attributes;

   ----------------------------------
   -- Declare_Component_Attributes --
   ----------------------------------

   procedure Declare_Component_Attributes
     (P : W_Section_Id;
      E : Entity_Id)
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
         Emit (P,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        =>
                    To_Local (E_Symb (Field, WNE_Attr_First_Bit)),
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => EW_Int_Type));

         Emit (P,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        =>
                    To_Local (E_Symb (Field, WNE_Attr_Last_Bit)),
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => EW_Int_Type));

         Emit (P,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        =>
                    To_Local (E_Symb (Field, WNE_Attr_Position)),
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => EW_Int_Type));

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
     (Section : W_Section_Id;
      Root    : Entity_Id)
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

      Emit (Section,
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
      Emit (Section,
            New_Function_Decl
              (Domain      => EW_Prog,
               Name        => To_Local (E_Symb (Root, WNE_Range_Check_Fun)),
               Binders     => R_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => EW_Unit_Type,
               Pre         => Pre_Cond));
   end Declare_Conversion_Check_Function;

   -----------------------------
   -- Declare_Rep_Record_Type --
   -----------------------------

   procedure Declare_Rep_Record_Type
     (P : W_Section_Id;
      E : Entity_Id)
   is
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

      procedure Declare_Conversion_Functions;
      --  Generate conversion functions from this type to the root type, and
      --  back.

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

      procedure Declare_Protected_Access_Functions;
      --  For each record field, declare an access program function, whose
      --  result is the same as the record field access, but there is a
      --  precondition (when needed).

      procedure Declare_Record_Type;
      --  Declare the record type

      function Discriminant_Check_Pred_Call
        (Field : Entity_Id;
         Arg   : W_Identifier_Id)
         return W_Pred_Id;
      --  Given a record field, return the a call to its discrimant check
      --  predicate, with the given argument. If that predicate is defined
      --  elsewhere (i.e. in the module for the root record type) prefix the
      --  call accordingly and add a conversion.

      function Extract_Extension_Fun return W_Identifier_Id;
      --  Return the name of the extract function for an extension component

      function New_Extension_Component_Expr (Ty : Entity_Id) return W_Expr_Id;
      --  Return the name of the special field representing extension
      --  components.

      function Extract_Fun
        (Field : Entity_Id;
         Rec   : Entity_Id;
         Local : Boolean := True)
         return W_Identifier_Id;
      --  Return the name of the extract function for an extension

      function Transform_Discrete_Choices
        (Case_N : Node_Id;
         Expr   : W_Term_Id)
         return W_Pred_Id;
      --  Wrapper for the function in Gnat2Why.Expr

      ---------------------
      -- Local Variables --
      ---------------------

      Root      : constant Entity_Id     := Root_Retysp (E);
      Is_Root   : constant Boolean       := Root = E;
      Ty_Name   : constant W_Name_Id     := To_Name (WNE_Rec_Rep);
      Abstr_Ty  : constant W_Type_Id     := New_Named_Type (Name => Ty_Name);
      Comp_Info : constant Component_Info_Map := Get_Variant_Info (E);

      A_Ident   : constant W_Identifier_Id :=
        New_Identifier (Name => "a", Typ => Abstr_Ty);
      R_Binder  : constant Binder_Array :=
        (1 => (B_Name => A_Ident,
               others => <>));

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
                         (Ada_Discr, Local => Is_Root, Rec => Root),
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

      ----------------------------------
      -- Declare_Conversion_Functions --
      ----------------------------------

      procedure Declare_Conversion_Functions is
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
                        Orig_Id := To_Why_Id (Orig, Rec => Root);

                        Field_From_Index := Field_From_Index + 1;
                        From_Root_Field (Field_From_Index) :=
                          New_Field_Association
                            (Domain => EW_Term,
                             Field  => Field_Id,
                             Value  =>
                               Insert_Simple_Conversion
                                 (Domain => EW_Term,
                                  To     => W_Type_Of_Component (Field, E),
                                  Expr   =>
                                    New_Record_Access
                                      (Name  => R_Field_Access,
                                       Field => Orig_Id,
                                       Typ   => W_Type_Of_Component (Orig, E)),
                                  Force_No_Slide => True));

                        Field_To_Index := Field_To_Index + 1;
                        To_Root_Field (Field_To_Index) :=
                          New_Field_Association
                            (Domain => EW_Term,
                             Field  => Orig_Id,
                             Value  =>
                               Insert_Simple_Conversion
                                 (Domain => EW_Term,
                                  To     => W_Type_Of_Component (Orig, E),
                                  Expr   =>
                                    New_Record_Access
                                      (Name  => E_Field_Access,
                                       Field => Field_Id,
                                       Typ   =>
                                         W_Type_Of_Component (Field, E)),
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
                                        +New_Extension_Component_Expr (Root),
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
                       + 1;  --  for the extension field of the current type;
                     Args   : W_Expr_Array (1 .. Num_Args);
                     Index  : Natural := 0;
                  begin
                     for Field of Get_Component_Set (E) loop
                        if No (Search_Component_In_Type (Root, Field)) then
                           Index := Index + 1;
                           Args (Index) :=
                             New_Record_Access
                             (Name  => E_Field_Access,
                              Field =>
                                To_Why_Id (Field, Local => True, Rec => E),
                              Typ   => W_Type_Of_Component (Field, E));
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
                        Field  => +New_Extension_Component_Expr (Root),
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

         pragma Assert (To_Root_Aggr'Last = To_Index);
         pragma Assert (From_Root_Aggr'Last = From_Index);

         Emit
           (P,
            New_Function_Decl
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_To_Base)),
               Binders     => R_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => EW_Abstract (Root),
               Def         =>
                 New_Record_Aggregate
                   (Associations => To_Root_Aggr)));
         Emit
           (P,
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

      -------------------------------
      -- Declare_Equality_Function --
      -------------------------------

      procedure Declare_Equality_Function is

         B_Ident : constant W_Identifier_Id :=
           New_Identifier (Name => "b", Typ => Abstr_Ty);

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
         --  @param Field_Type ada type of the component, it is the enclosing
         --         type if Is_Private is True
         --  @return Equality of field_id from A and B.

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
                  A_F_Access : constant W_Expr_Id :=
                    (if Is_Discr then
                        New_Record_Access
                          (Name  => A_Access,
                           Field => Field_Id,
                           Typ   => EW_Abstract (Field_Type))
                     else
                        New_Init_Wrapper_Value_Access
                          (Ada_Node => Empty,
                           E        => Field_Type,
                           Name     => New_Record_Access
                             (Name  => A_Access,
                              Field => Field_Id,
                              Typ   => EW_Init_Wrapper
                                (Field_Type, EW_Abstract)),
                           Domain   => EW_Term));
                  B_F_Access : constant W_Expr_Id :=
                    (if Is_Discr then
                        New_Record_Access
                          (Name  => B_Access,
                           Field => Field_Id,
                           Typ   => EW_Abstract (Field_Type))
                     else
                        New_Init_Wrapper_Value_Access
                          (Ada_Node => Empty,
                           E        => Field_Type,
                           Name     => New_Record_Access
                             (Name  => B_Access,
                              Field => Field_Id,
                              Typ   => EW_Init_Wrapper
                                (Field_Type, EW_Abstract)),
                           Domain   => EW_Term));

               begin
                  return +New_Ada_Equality
                    (Typ    => Field_Type,
                     Domain => EW_Pred,
                     Left   => A_F_Access,
                     Right  => B_F_Access);
               end;
            end if;
         end New_Field_Equality;

      --  Start of processing for Declare_Equality_Function

      begin
         if not Is_Limited_View (E) then
            declare
               Condition : W_Pred_Id := True_Pred;
               Discr     : Entity_Id;

            begin
               --  Compare discriminants

               if Has_Discriminants (E) then
                  Discr := First_Discriminant (E);
                  loop
                     declare
                        Discrs_Id  : constant W_Identifier_Id :=
                          To_Ident (WNE_Rec_Split_Discrs);
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
               end if;

               --  Compare Fields

               declare
                  Comp_Set : Node_Sets.Set renames Get_Component_Set (E);
               begin
                  if not Comp_Set.Is_Empty then
                     declare
                        Conjuncts : W_Expr_Array
                          (1 .. Positive (Comp_Set.Length));
                        I : Positive := 1;
                     begin
                        for Comp of Comp_Set loop
                           declare
                              Fields_Id      : constant W_Identifier_Id :=
                                To_Ident (WNE_Rec_Split_Fields);
                              Field_Id       : constant W_Identifier_Id :=
                                To_Why_Id (Comp, Local => True, Rec => E);
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
                              Conjuncts (I) :=
                                (if Always_Present then +Comparison
                                 else
                                    New_Connection
                                   (Domain => EW_Pred,
                                    Op     => EW_Imply,
                                    Left   =>
                                      +Discriminant_Check_Pred_Call
                                      (Comp, A_Ident),
                                    Right  => +Comparison));
                              I := I + 1;
                           end;
                        end loop;
                        Condition :=
                          +New_And_Expr (+Condition,
                                         New_And_Expr (Conjuncts, EW_Pred),
                                         EW_Pred);
                     end;
                  end if;
               end;

               --  For simple private types, equality is an uninterpreted
               --  function. For now, it is as good as using equality on
               --  EW_Private. If at some point, we choose to assume more about
               --  equality on private types, we may want to replace this one
               --  with a clone of an appropriate equality module.

               Emit
                 (P,
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
                       (if Is_Simple_Private_Type (E) then Why_Empty
                        else New_Conditional
                          (Domain    => EW_Term,
                           Condition => +Condition,
                           Then_Part => +True_Term,
                           Else_Part => +False_Term))));
            end;
         end if;

         --  Declare the dispatching equality function in root types
         if Is_Root and then Is_Tagged_Type (E) then
            Emit
              (P,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (E_Symb (E, WNE_Dispatch_Eq)),
                  Return_Type => EW_Bool_Type,
                  Binders     => R_Binder &
                    Binder_Array'(1 => Binder_Type'(B_Name => B_Ident,
                                                    others => <>)),
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set));
         end if;
      end Declare_Equality_Function;

      ----------------------------------
      -- Declare_Extraction_Functions --
      ----------------------------------

      procedure Declare_Extraction_Functions (Components : Node_Lists.List) is
         X_Ident         : constant W_Identifier_Id :=
           New_Identifier (Name => "x", Typ => EW_Private_Type);
         Binder          : constant Binder_Array :=
           (1 => (B_Name => X_Ident,
                  others => <>));
         Hide_Name       : constant W_Identifier_Id :=
           To_Ident (WNE_Hide_Extension);
         Extract_Func    : constant W_Identifier_Id := Extract_Extension_Fun;
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
                                 Typ  => W_Type_Of_Component (Field, E)),
               others => <>);
         end loop;

         --  the extension field in the current type is also part of the
         --  extension field in the root type

         Index := Index + 1;
         Hide_Binders (Index) :=
           (B_Name => To_Local (E_Symb (E, WNE_Rec_Extension)),
            others => <>);

         pragma Assert (Index = Num_Hide_Params);

         --  function hide__ext__ (comp1 : typ1; .. ; x : __private)
         --                       : __private

         Emit (P,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => Hide_Name,
                  Binders     => Hide_Binders,
                  Labels      => Symbol_Sets.Empty_Set,
                  Location    => No_Location,
                  Return_Type => EW_Private_Type));

         for Field of Components loop

            --  function extract__<comp> (x : __private) : <typ>

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
                     Typ      => W_Type_Of_Component (Field, E))
                  else Why_Empty);
            begin
               Emit (P,
                     New_Function_Decl
                       (Domain      => EW_Pterm,
                        Name        => Extract_Fun (Field, Rec => E),
                        Binders     => Binder,
                        Labels      => Symbol_Sets.Empty_Set,
                        Location    => No_Location,
                        Return_Type => W_Type_Of_Component (Field, E),
                        Def         => Definition));
            end;

            --  Declare an axiom for the extraction function stating:
            --  forall .... extract__<comp> (hide__ext (...)) = comp

            Emit (P,
                  New_Guarded_Axiom
                    (Name     =>
                       NID (Img (Get_Symb
                         (Get_Name (Extract_Fun (Field, Rec => E))))
                         & "__conv"),
                     Binders  => Hide_Binders,
                     Def      => +New_Comparison
                       (Symbol => Why_Eq,
                        Left   => New_Call
                          (Domain  => EW_Term,
                           Name    => Extract_Fun (Field, Rec => E),
                           Args    =>
                             (1 => New_Call
                                  (Domain  => EW_Term,
                                   Name    => Hide_Name,
                                   Binders => Hide_Binders,
                                   Typ     => EW_Private_Type)),
                           Typ     => W_Type_Of_Component (Field, E)),
                        Right  => +New_Identifier
                          (Name => Full_Name (Field),
                           Typ  => W_Type_Of_Component (Field, E)),
                        Domain => EW_Term)));

         end loop;

         --  function extract__ext__ (x : __private) : __private

         Emit (P,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => Extract_Func,
                  Binders     => Binder,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set,
                  Return_Type => EW_Private_Type));
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

      ----------------------------------------
      -- Declare_Protected_Access_Functions --
      ----------------------------------------

      procedure Declare_Protected_Access_Functions is

         procedure Declare_Protected_Access_Function (Field : Entity_Id);
         --  Declare a program access function for a field, whose precondition
         --  is Discriminant_Check_Pred_Name. Note that [Precond] has been
         --  computed so that it uses the correct predicate name, whether it
         --  has been defined here or in the root type. In the case of a
         --  discriminant, the precondition is simply "true".
         --  @param Field a record field or disciminant.

         ---------------------------------------
         -- Declare_Protected_Access_Function --
         ---------------------------------------

         procedure Declare_Protected_Access_Function (Field : Entity_Id) is
            Why_Name  : constant W_Identifier_Id :=
              (if Is_Root or else Ekind (Field) /= E_Discriminant then
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
               else Discriminant_Check_Pred_Call (Field, A_Ident));
         begin
            Emit (P,
                  New_Function_Decl
                    (Domain      => EW_Prog,
                     Name        => Prog_Name,
                     Binders     => R_Binder,
                     Location    => No_Location,
                     Labels      => Symbol_Sets.Empty_Set,
                     Return_Type => W_Type_Of_Component (Field, E),
                     Pre         => Precond,
                     Post        => Post));
         end Declare_Protected_Access_Function;

      --  Start of processing for Declare_Protected_Access_Functions

      begin
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
                  Emit (P,
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

      procedure Declare_Record_Type is
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
            Emit_Hardcoded_Type_Declaration (P, E);

         --  Simple private types are translated directly as EW_Private_Type

         elsif Is_Simple_Private_Type (E) then
            Emit (P,
                  New_Type_Decl
                    (Name => To_String (WNE_Rec_Rep)));
         else

            --  Generate a record type for E's discriminants if E is a root
            --  type and use Root's record type for discriminants otherwise.

            if Num_Discrs > 0 then
               declare
                  Discr_Name : constant W_Name_Id :=
                    To_Name (WNE_Rec_Split_Discrs);
                  Discr      : Entity_Id := First_Discriminant (E);
               begin
                  if Is_Root then
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
                       (Section      => P,
                        Name         => Discr_Name,
                        Binders      => Binders_D,
                        SPARK_Record => True);

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
                          Typ   => W_Type_Of_Component (Field, E)),
                     Labels   =>
                       Get_Model_Trace_Label
                         (E               => Field,
                          Is_Record_Field => True),
                     Ada_Node => Field,
                     others   => <>);
                  Index := Index + 1;
               end loop;

               --  For tagged types, add a field of type __private representing
               --  the unknown extension components.

               if Is_Tagged_Type (E) then
                  Binders_F (Index) :=
                    (B_Name => To_Local (E_Symb (E, WNE_Rec_Extension)),
                     others => <>);
                  Index := Index + 1;
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

            pragma Assert (Index_All = Num_All + 1);

            Emit_Record_Declaration (Section      => P,
                                     Name         => Ty_Name,
                                     Binders      => Binders_A,
                                     SPARK_Record => True);
         end if;
      end Declare_Record_Type;

      ----------------------------------
      -- Discriminant_Check_Pred_Call --
      ----------------------------------

      function Discriminant_Check_Pred_Call
        (Field : Entity_Id;
         Arg   : W_Identifier_Id)
         return W_Pred_Id is
      begin
         return
           New_Call
             (Name => Discriminant_Check_Pred_Name (E, Field, True),
              Args => (1 => +Arg));
      end Discriminant_Check_Pred_Call;

      ---------------------------
      -- Extract_Extension_Fun --
      ---------------------------

      function Extract_Extension_Fun return W_Identifier_Id is
      begin
         return New_Identifier (Name => To_String (WNE_Extract_Prefix) &
                                        To_String (WNE_Rec_Extension_Suffix));
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
      -- New_Extension_Component_Expr --
      ----------------------------------

      function New_Extension_Component_Expr (Ty : Entity_Id) return W_Expr_Id
      is
      begin
         return +E_Symb (Ty, WNE_Rec_Extension);
      end New_Extension_Component_Expr;

      --------------------------------
      -- Transform_Discrete_Choices --
      --------------------------------

      function Transform_Discrete_Choices
        (Case_N : Node_Id;
         Expr   : W_Term_Id)
         return W_Pred_Id
      is
      begin
         return +Gnat2Why.Expr.Transform_Discrete_Choices
           (Choices      => Discrete_Choices (Case_N),
            Choice_Type  => Empty,  --  not used for predicates, can be empty
            Matched_Expr => +Expr,
            Cond_Domain  => EW_Pred,
            Params       => Logic_Params);
      end Transform_Discrete_Choices;

   --  Start of processing for Declare_Rep_Record_Type

   begin
      --  For types which have a private part, declare a new uninterpreted type
      --  for the private part as well as a new uninterpreted equality
      --  function.

      if Has_Private_Part (E) then
         declare
            Priv_Name : constant W_Name_Id    :=
              To_Local (E_Symb (E, WNE_Private_Type));
            Priv_Ty   : constant W_Type_Id    :=
              New_Named_Type (Name => Priv_Name);
            Binders   : constant Binder_Array :=
              (1 => (B_Name => New_Identifier (Name => "a", Typ => Priv_Ty),
                     others => <>),
               2 => (B_Name => New_Identifier (Name => "b", Typ => Priv_Ty),
                     others => <>));

         begin
            Emit (P,
                  New_Type_Decl
                    (Name  => Img (Get_Symb (Priv_Name))));
            Emit
              (P,
               New_Function_Decl
                 (Domain      => EW_Pterm,
                  Name        => To_Local (E_Symb (E, WNE_Private_Eq)),
                  Binders     => Binders,
                  Return_Type => +EW_Bool_Type,
                  Location    => No_Location,
                  Labels      => Symbol_Sets.Empty_Set));
         end;
      end if;

      Declare_Record_Type;

      --  We need to delare conversion functions before the protected access
      --  functions, because the former may be used in the latter

      if not Is_Root then
         pragma Assert (not Is_Simple_Private_Type (E));

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
              (Domain      => EW_Pterm,
               Name        => To_Local (E_Symb (E, WNE_To_Base)),
               Binders     => R_Binder,
               Location    => No_Location,
               Labels      => Symbol_Sets.Empty_Set,
               Return_Type => Abstr_Ty,
               Def         => +A_Ident));
         Emit
           (P,
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
         Declare_Protected_Access_Functions;
      end if;

      Declare_Equality_Function;
   end Declare_Rep_Record_Type;

   ----------------------------------
   -- Discriminant_Check_Pred_Name --
   ----------------------------------

   function Discriminant_Check_Pred_Name
     (E     : Entity_Id;
      Field : Entity_Id;
      Local : Boolean)
      return W_Identifier_Id
   is
      Orig : constant Entity_Id := Representative_Component (Field);
      Name : constant String := Full_Name (Orig) & "__pred";
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
                   Get_Name (E_Symb (Root_Retysp (E),
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
      Discr_Expr   : out W_Expr_Id;
      Field_Assocs : out W_Field_Association_Array)
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
            Domain   => Term_Domain (Domain),
            Name     => Expr,
            Ty       => Anc_Ty);
      else
         Discr_Expr := Why_Empty;
      end if;

      for Anc_Comp of Get_Component_Set (Anc_Ty) loop

         Component := Search_Component_In_Type (Ty, Anc_Comp);

         pragma Assert (Present (Component));

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

   ---------------------------
   -- Get_Rep_Record_Module --
   ---------------------------

   function Get_Rep_Record_Module (E : Entity_Id) return W_Module_Id is
      Ancestor : constant Entity_Id := Oldest_Parent_With_Same_Fields (E);
      Name     : constant String :=
        Full_Name (Ancestor) & To_String (WNE_Rec_Rep);
   begin
      return New_Module (File => No_Symbol,
                         Name => Name);
   end Get_Rep_Record_Module;

   ---------------------------------------
   -- Insert_Subtype_Discriminant_Check --
   ---------------------------------------

   function Insert_Subtype_Discriminant_Check
     (Ada_Node : Node_Id;
      Check_Ty : Entity_Id;
      Expr     : W_Prog_Id)
      return W_Prog_Id
   is
      Root : constant Entity_Id := Root_Retysp (Check_Ty);
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

      declare
         Tmp_Expr : constant W_Expr_Id := New_Temp_For_Expr (+Expr);
      begin
         return
           +Binding_For_Temp
             (Ada_Node => Ada_Node,
              Domain   => EW_Prog,
              Tmp      => Tmp_Expr,
              Context  => +Sequence
                (Ada_Node => Ada_Node,
                 Left     => +New_VC_Call
                   (Ada_Node => Ada_Node,
                    Name     => Range_Check_Name (Root, RCK_Range),
                    Progs    => Prepare_Args_For_Subtype_Check
                      (Check_Ty, Tmp_Expr),
                    Domain   => EW_Prog,
                    Reason   => VC_Discriminant_Check,
                    Typ      => Get_Type (+Expr)),
                 Right    => +Tmp_Expr));
      end;
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
         Name     => M_Compat_Tags.Compat_Tags_Id,
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
         else Root_Retysp (Ty));
      Call_Id   : constant W_Identifier_Id := To_Why_Id (Field, Rec => Rec);

      Ret_Ty    : constant W_Type_Id :=
        (if Is_Part_Of_Protected_Object (Field) then
            EW_Abstract (Etype (Field))
         else
            W_Type_Of_Component (Search_Component_In_Type (Ty, Field), Empty));
      Top_Field : constant W_Expr_Id :=
        (if Ekind (Field) = E_Discriminant
         then New_Discriminants_Access (Ada_Node, Domain, Name, Ty)
         else New_Fields_Access (Ada_Node, Domain, Name, Ty));
   begin
      if Domain = EW_Prog
        and then Ekind (Field) = E_Component
        and then Retysp_Kind (Rec) in Private_Kind | Record_Kind
        and then Has_Variant_Info (Rec, Field)
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
     (Ada_Node     : Node_Id := Empty;
      Domain       : EW_Domain;
      Discr_Expr   : W_Expr_Id;
      Field_Assocs : W_Field_Association_Array;
      Ty           : Entity_Id;
      Anc_Ty       : Entity_Id := Empty)
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
            Field    => E_Symb (Ty, WNE_Rec_Split_Discrs),
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
            --  aggregate. Those are fields not visible in the type and not
            --  already present in the ancestor type.

            for Comp of Get_Component_Set (Ty) loop
               if not Component_Is_Present_In_Type (Ty, Comp)
                 and then
                   (No (Anc_Ty)
                    or else No (Search_Component_In_Type (Anc_Ty, Comp)))
               then

                  pragma Assert (not Is_Type (Comp));

                  Index := Index + 1;
                  All_Field_Assocs (Index) :=
                    New_Field_Association
                      (Domain => Domain,
                       Field  => To_Why_Id (Comp, Rec => Ty),
                       Value  => Reconstruct_Init_Wrapper
                         (Ty    => Etype (Comp),
                          Value => Why_Default_Value (EW_Term, Etype (Comp))));
               end if;
            end loop;

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

   function New_Ada_Record_Aggregate
     (Ada_Node     : Node_Id := Empty;
      Domain       : EW_Domain;
      Discr_Assocs : W_Field_Association_Array;
      Field_Assocs : W_Field_Association_Array;
      Ty           : Entity_Id)
      return W_Expr_Id
   is
      Discr_Expr : constant W_Expr_Id :=
        (if Count_Discriminants (Ty) > 0
         then New_Record_Aggregate (Associations => Discr_Assocs)
         else Why_Empty);

   begin
      return New_Ada_Record_Aggregate
        (Ada_Node, Domain, Discr_Expr, Field_Assocs, Ty);
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
   begin
      --  Do not emit checks for part of variables or discriminants

      if Ekind (Field) = E_Component then
         return
           New_Call
             (Ada_Node => Ada_Node,
              Name     => Discriminant_Check_Pred_Name (Ty, Field, False),
              Args     => (1 => Name),
              Domain   => Domain,
              Typ      => EW_Bool_Type);
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
                      Value  => Reconstruct_Init_Wrapper
                        (Ty    => Retysp (Etype (Field)),
                         Value => Value)))),
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
     (New_Record_Access
        (Ada_Node => Ada_Node,
         Field    => E_Symb (Ty, WNE_Rec_Split_Discrs),
         Name     => Name));

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
     (New_Record_Access
         (Ada_Node => Ada_Node,
          Field    => E_Symb (Ty, WNE_Rec_Split_Fields),
          Name     => Name));

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
      Has_Tag         : constant Boolean :=
        (Is_Tagged_Type (Ty)
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
                  Ty     => Ty));
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
                  Typ      => EW_Abstract (Ty)));
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
      Num_Discr : constant Natural := Count_Discriminants (Check_Ty);
      Args      : W_Expr_Array (1 .. Num_Discr + 1);
      Count     : Natural := 1;
      Discr     : Entity_Id := First_Discriminant (Check_Ty);
      Elmt      : Elmt_Id := First_Elmt (Discriminant_Constraint (Check_Ty));

   begin
      Args (Num_Discr + 1) := New_Discriminants_Access
        (Domain => EW_Term,
         Name   => Expr,
         Ty     => Get_Ada_Node (+Get_Type (Expr)));

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

   function Record_From_Split_Form
     (I           : Item_Type;
      Ref_Allowed : Boolean)
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

end Why.Gen.Records;
