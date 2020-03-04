------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      W H Y - G E N - R E C O R D S                       --
--                                                                          --
--                                 S p e c                                  --
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

with Gnat2Why.Util;        use Gnat2Why.Util;
with SPARK_Atree;          use SPARK_Atree;
with SPARK_Atree.Entities; use SPARK_Atree.Entities;
with SPARK_Util.Types;     use SPARK_Util.Types;
with Types;                use Types;
with Why.Gen.Binders;      use Why.Gen.Binders;
with Why.Ids;              use Why.Ids;
with Why.Sinfo;            use Why.Sinfo;
with Why.Types;            use Why.Types;

package Why.Gen.Records is
   --  This package encapsulates the encoding of Ada records into Why. This
   --  also includes records with variant parts.

   procedure Declare_Ada_Record
     (P : W_Section_Id;
      E : Entity_Id) with
     Pre => Ekind (E) in E_Record_Type | E_Record_Subtype |
                         Private_Kind  | Concurrent_Kind;
   --  Emit all necessary Why3 declarations to support Ada records. This also
   --  supports variant records, private types and concurrent types.
   --  @param P the Why section to insert the declaration
   --  @param Theory the theory in which to insert the type declaration
   --  @param E the type entity to translate

   procedure Declare_Init_Wrapper_For_Record
     (P : W_Section_Id;
      E : Entity_Id) with
     Pre => Ekind (E) in E_Record_Type | E_Record_Subtype |
                         Private_Kind
     and then Might_Contain_Relaxed_Init (E);

   procedure Create_Rep_Record_Theory_If_Needed
     (P : W_Section_Id;
      E : Entity_Id)
   with
     Pre => Ekind (E) in E_Record_Type | E_Record_Subtype |
                         Private_Kind  | Concurrent_Kind;
   --  Create a module for the representative type of a record if needed. It
   --  contains a why record type named WNE_Rec_Rep and all the needed
   --  functions and attributes except for the tag of tagged types.

   function New_Ada_Record_Access
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Field    : Entity_Id;
      Ty       : Entity_Id)
      return W_Expr_Id;
   --  Generate a Why3 expression that corresponds to the access to an Ada
   --  record field.
   --  @param Ada_Node  the Ada Node that corresponds to the record access
   --  @param Domain    the domain of the Why expression
   --  @param Name      the prefix for the record expression, as a Why
   --                     expression
   --  @param Field     the field access, as an Ada entity
   --  @param Ty        the type of the record
   --  @return a Why expression which corresponds to the Ada record
   --    access

   function New_Ada_Record_Check_For_Field
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Field    : Entity_Id;
      Ty       : Entity_Id)
      return W_Expr_Id;
   --  Generate a Why3 expression that corresponds to the cases where a record
   --  field is present in an Ada record.
   --  @param Ada_Node
   --  @param Domain  the domain of the Why expression
   --  @param Name    the prefix of the record expression
   --  @param Field   the field access as an Ada entity
   --  @param Ty      the type of the record, as Ada entity
   --  @return a Why expression that checks that the field access is allowed
   --          for that expression

   function New_Ada_Record_Update
     (Ada_Node : Node_Id;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Field    : Entity_Id;
      Value    : W_Expr_Id)
      return W_Expr_Id;
   --  Generate a Why3 expression that corresponds to the update to an Ada
   --  record field. Emit all necessary checks.
   --  Note that this function does not generate an assignment, instead it
   --  returns a functional update. In the case of simple records, it will look
   --  like
   --    { name with field = value }
   --  The assignment, if required, needs to be generated by the caller.

   function New_Ada_Record_Update
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Updates  : W_Field_Association_Array)
      return W_Expr_Id;
   --  Generate an update to a record. The associations in Updates should only
   --  modify normal fields (not discrimiants).

   function New_Ada_Record_Aggregate
     (Ada_Node     : Node_Id := Empty;
      Domain       : EW_Domain;
      Discr_Assocs : W_Field_Association_Array;
      Field_Assocs : W_Field_Association_Array;
      Ty           : Entity_Id;
      Init_Wrapper : Boolean := False)
      return W_Expr_Id;
   --  Generate a record aggregate of ada type Ty from the association in
   --  Discr_Assocs and Field_Assocs.

   function New_Ada_Record_Aggregate
     (Ada_Node     : Node_Id := Empty;
      Domain       : EW_Domain;
      Discr_Expr   : W_Expr_Id;
      Field_Assocs : W_Field_Association_Array;
      Ty           : Entity_Id;
      Init_Wrapper : Boolean := False;
      Anc_Ty       : Entity_Id := Empty)
      return W_Expr_Id;
   --  @param Ada_Node    node for the aggregate if any
   --  @param Domain      domain for the translation
   --  @param Discr_Expr  expression for the whole top-level field for
   --                     discriminants
   --  @param Field_Assoc associations for the record's fields
   --  @param Ty          Ada type of the aggregate
   --  @param Anc_Ty      type of the aggregate's ancestor part if any
   --  Same as above except that discriminant associations are given as a
   --  whole.

   procedure Generate_Associations_From_Ancestor
     (Ada_Node     : Node_Id := Empty;
      Domain       : EW_Domain;
      Expr         : W_Expr_Id;
      Anc_Ty       : Entity_Id;
      Ty           : Entity_Id;
      Discr_Expr   : out W_Expr_Id;
      Field_Assocs : out W_Field_Association_Array);
   --  Generate a record aggregate of ada type Ty from the association in
   --  Discr_Assocs and Field_Assocs.

   function New_Discriminants_Access
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Ty       : Entity_Id)
      return W_Expr_Id;
   --  Generate a Why3 expression that corresponds to an access to the
   --  top-level field for discriminants.

   function New_Discriminants_Update
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Value    : W_Expr_Id;
      Ty       : Entity_Id)
      return W_Expr_Id;
   --  Generate a Why3 expression that corresponds to an update of the
   --  top-level field for discriminants.

   function New_Fields_Access
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Ty       : Entity_Id)
      return W_Expr_Id;
   --  Generate a Why3 expression that corresponds to an access to the
   --  top-level field for fields.

   function New_Fields_Update
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Value    : W_Expr_Id;
      Ty       : Entity_Id)
      return W_Expr_Id;
   --  Generate a Why3 expression that corresponds to an update of the
   --  top-level field for fields.

   function New_Tag_Access
     (Ada_Node : Node_Id := Empty;
      Domain   : EW_Domain;
      Name     : W_Expr_Id;
      Ty       : Entity_Id)
      return W_Expr_Id;
   --  Generate a Why3 expression that corresponds to an access to the
   --  additional field introduced for records' tag.

   function New_Tag_Update
     (Ada_Node  : Node_Id := Empty;
      Domain    : EW_Domain;
      Name      : W_Expr_Id;
      From_Expr : W_Expr_Id := Why_Empty;
      Ty        : Entity_Id)
      return W_Expr_Id;
   --  Generate a Why3 expression that corresponds to an update to the
   --  additional field introduced in records for the 'Tag attribute.
   --  @param Ada_Node ada node associated to the object
   --  @param Domain domain of the expression
   --  @param Name name of the record object to update
   --  @param From_Expr expression from which the attribute should be taken
   --  if present. Otherwise, tag attribute is initialized to the default value
   --  of Ty, that is, 'Tag is the Ty's tag for specific tagged types.
   --  @result Name updated with values of From_Expr attribute if present and
   --     default one otherwise.

   function Insert_Subtype_Discriminant_Check
     (Ada_Node : Node_Id;
      Check_Ty : Entity_Id;
      Expr     : W_Prog_Id)
      return W_Prog_Id;
   --  Given a record subtype and an expression, add a call to the subtype
   --  discriminant check function, to generate a discriminant check.

   function Prepare_Args_For_Subtype_Check
     (Check_Ty : Entity_Id;
      Expr     : W_Expr_Id)
      return W_Expr_Array;
   --  Given a record type, compute the argument array that can be used
   --  together with its subtype check predicate of program function. The
   --  last argument is actually the given expression itself.

   function Insert_Tag_Check
     (Ada_Node : Node_Id;
      Check_Ty : Entity_Id;
      Expr     : W_Prog_Id)
      return W_Prog_Id;
   --  Given a record subtype and an expression, add a call to compatible_tag
   --  function to generate a tag check.

   function Record_From_Split_Form
     (I           : Item_Type;
      Ref_Allowed : Boolean)
      return W_Expr_Id
   with
       Pre => I.Kind = DRecord;
   --  Reconstructs a complete record from an item in split form.

   function Record_From_Split_Form
     (Ada_Node     : Node_Id := Empty;
      A            : W_Expr_Array;
      Ty           : Entity_Id;
      Init_Wrapper : Boolean := False)
      return W_Expr_Id;
   --  Reconstructs a complete record of type Ty from an array of expressions
   --  representing a split form. A should contain first the fields, then the
   --  discriminants, the 'Constrained attribute and the 'Tag attribute.

   function Field_Type_For_Discriminants (E : Entity_Id) return W_Type_Id with
     Pre => Is_Type (E) and then Has_Discriminants (E);
   --  Type of the top-level Why3 field for discriminants of E.

   function Field_Type_For_Fields
     (E            : Entity_Id;
      Init_Wrapper : Boolean := False) return W_Type_Id
   with
     Pre => Is_Type (E) and then Count_Why_Regular_Fields (E) > 0;
   --  Type of the top-level Why3 field for fields of E.

   function Record_Type_Is_Clone (E : Entity_Id) return Boolean;
   --  Return True if we do not produce a new type declaration for E but rather
   --  clone an existing one.
   --  This is used so that we can know if we need to create new references

   function Record_Type_Cloned_Subtype (E : Entity_Id) return Entity_Id with
     Pre => Record_Type_Is_Clone (E);
   --  Return the existing type declaration that has been cloned for E

   function Oldest_Parent_With_Same_Fields (E : Entity_Id) return Entity_Id;

   generic
      with function Build_Predicate_For_Discr
        (D_Expr : W_Term_Id; D_Ty : Entity_Id; E : Entity_Id)
         return W_Pred_Id;
      with function Build_Predicate_For_Field
        (F_Expr : W_Term_Id; F_Ty : Entity_Id; E : Entity_Id)
         return W_Pred_Id;
   function Build_Predicate_For_Record
     (Expr : W_Term_Id; Ty : Entity_Id) return W_Pred_Id;
   --  Construct a predicate:
   --  Build_Predicate_For_Discr <Expr>.rec__d1 /\ ...
   --  /\ (check_for_f1 <Expr> -> Build_Predicate_For_Field <Expr>.rec__f1)
   --  /\ ..
   --  /\ (check_for_fn <Expr> -> Build_Predicate_For_Field <Expr>.rec__fn)

end Why.Gen.Records;
