------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              S P A R K _ D E F I N I T I O N - A N N O T A T E           --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2011-2026, AdaCore                     --
--              Copyright (C) 2014-2026, Capgemini Engineering              --
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
with Atree;       use Atree;
with Einfo.Utils; use Einfo.Utils;
with SPARK_Util;  use SPARK_Util;
with VC_Kinds;    use VC_Kinds;

package SPARK_Definition.Annotate is

   --  This package deals with justification of individual messages using
   --  pragma Annotate.

   --  The user can suppress check messages emitted by GNATprove by putting a
   --  pragma Annotate in the source code. An example is the following:

   --    return (X + Y) / (X - Y);
   --    pragma Annotate (GNATprove, False_Positive,
   --                     "divide by zero", "reviewed by John Smith");

   --  The pragma has the following form:
   --    pragma Annotate (GNATprove, Category, Pattern, Reason);

   --  where
   --    GNATprove   is a fixed identifier
   --    Category    is one of False_Positive or Intentional
   --    Pattern     is a string literal describing the pattern of the messages
   --                which shall be suppressed
   --    Reason      is a string literal providing a reason for the
   --                suppression.

   --  All arguments should be provided.

   --  The category has no impact on the behavior of the tool, but the idea
   --  is that False_Positive should be used to suppress checks that cannot
   --  occcur, but GNATprove was unable to detect this; Intentional indicates
   --  that the condition can occure but is not considered to be a bug.

   --  Pattern should be a substring of the GNATprove check message to be
   --  suppressed.

   --  Reason is any string that the user can use to provide a reason for the
   --  suppression. This reason may be present in a GNATprove report.

   --  Placement rules are as follows: in a statement list or declaration list,
   --  pragma Annotate applies to the preceding item in the list, ignoring
   --  other pragma Annotate. If there is no preceding item, the pragma applies
   --  to the enclosing entity. If the preceding item is a subprogram body, the
   --  pragma applies both to the body and the spec of the subprogram.

   --  This package also stores additional uses of pragma Annotate.

   --  A pragma Annotate for Iterable_For_Proof has the following form:
   --    pragma Annotate (GNATprove, Iterable_For_Proof, Kind, Entity => E);

   --  where
   --    GNATprove            is a fixed identifier
   --    Iterable_For_Proof   is a fixed identifier
   --    Kind                 must be one of "Model" or "Contains"
   --    E                    is a function entity

   --  If Kind is "Model" then E must have the following signature:
   --    function Get_Model (C : Container_Type) return Model_Type;

   --  where Container_Type and Model_Type both have an Iterable aspect that
   --  allows for ... of quantification on compatible element types.

   --  When such an annotation is provided, for ... of quantification on a
   --  container C is translated as for ... of quantification on its model
   --  Get_Model (C) instead.

   --  If Kind is "Contains" then E must have the following signature:
   --    function Contains (C : Container_Type; X : Element) return Boolean;

   --  where Container_Type have an Iterable aspect that allows for ... of
   --  quantification on elements of type Element.

   --  When such an annotation is provided, for ... of quantification on a
   --  container C is translated in Why3 as quantification over elements
   --  using the provided Contains function.

   --  A pragma Annotate for Inline_For_Proof has the following form:
   --    pragma Annotate (GNATprove, Inline_For_Proof, Entity => E);

   --  where
   --    GNATprove           is a fixed identifier
   --    Inline_For_Proof    is a fixed identifier
   --    E                   is a function entity

   --  and E must either be an expression function or have the following
   --  signature:
   --    function E (...) return ... with
   --      Post => E'Result = Expr;

   --  where Expr must not contain any forward reference to entities defined
   --  after E.

   --  When such an annotation is provided, E is translated as a function
   --  definition in Why3 on which the label "inline" is set so that gnatwhy3
   --  inlines its definition for provers.

   --  A pragma Annotate for logical equality has the following form:
   --    pragma Annotate (GNATprove, Logical_Equal, Entity => E);

   --  where
   --    GNATprove           is a fixed identifier
   --    Logical_Equal       is a fixed identifier
   --    E                   is a function with the signature of an equality
   --                        function and no visible body.

   --  When such an annotation is provided for a function E, is is assumed to
   --  be an application of the logical "=" operator of Why3.

   --  A pragma Annotate for ownership can be applied either on a type, a
   --  constant, or a function. On a type, it has the following form:
   --    pragma Annotate
   --        (GNATprove, Ownership, ["Needs_Reclamation",] Entity => E);

   --  where
   --    GNATprove           is a fixed identifier
   --    Ownership           is a fixed identifier
   --    Needs_Reclamation   is a fixed string
   --    E                   is a type entity

   --  and E shall be a private type (tagged or not, but not a private
   --  extension) whose full view is in a part annotated with
   --  SPARK_Mode => Off.

   --  When such an annotation is provided for a type E, it is treated by the
   --  SPARK tool as if it contained a subcomponent of an access-to-variable
   --  type. If Needs_Reclamation is supplied, a check will be emitted to make
   --  sure that no values are left unreclaimed.
   --
   --  On a function, it has one of the following forms:
   --    pragma Annotate
   --        (GNATprove, Ownership, "Is_Reclaimed", Entity => E);
   --    pragma Annotate
   --        (GNATprove, Ownership, "Needs_Reclamation", Entity => E);

   --  where
   --    GNATprove           is a fixed identifier
   --    Ownership           is a fixed identifier
   --    Is_Reclaimed        is a string
   --    Needs_Reclamation   is a string
   --    E                   is a function entity

   --  and E shall have a single parameter of a type annotated with ownership
   --  that needs reclamation and shall return a boolean.
   --
   --  On a constant, it has the following forms:
   --    pragma Annotate
   --        (GNATprove, Ownership, "Reclaimed_Value", Entity => E);

   --  where
   --    GNATprove           is a fixed identifier
   --    Ownership           is a fixed identifier
   --    Reclaimed_Value     is a string
   --    E                   is a constanr entity

   --  and E shall be a constant of a type annotated with ownership that needs
   --  reclamation.

   --  When such an annotation is provided for a function E, this function is
   --  used when checking reclamation of objects of E's formal parameter type.
   --  For a given type, there shall not be more than one such function
   --  provided. If there is none, the reclamation checks will be unprovable.

   --  A pragma Annotate for automatic instantiation of lemmas has the
   --  following form:
   --    pragma Annotate (GNATprove, Automatic_Instantiation, Entity => E);

   --  where
   --    GNATprove               is a fixed identifier
   --    Automatic_Instantiation is a fixed identifier
   --    E                       is a ghost procedure with no Globals nor
   --                            mutable parameters.

   --  The ghost procedure E shall be located directly after a function
   --  declaration, possibly separated by some pragmas and other ghost
   --  procedures with automatic instantiation. The procedure will be
   --  transformed into an axiom which will be included whenever the function
   --  is called.

   --  A pragma Annotate for specialized handling of static access-to-function
   --  parameters has the following form:
   --    pragma Annotate (GNATprove, Higher_Order_Specialization, Entity => E);

   --  where
   --    GNATprove                   is a fixed identifier
   --    Higher_Order_Specialization is a fixed identifier
   --    E                           is a function or lemma procedure with
   --                                parameters of an anonymous
   --                                access-to-function type.

   --  The subprogram E shall not be volatile, dispatching, nor a borrowing
   --  traversal function. If it is a procedure, it shall be a lemma function -
   --  ghost and no outputs. Its parameters shall only occur in contracts in
   --  dereferences and as actuals in calls to functions annotated with
   --  Higher_Order_Specialization (the actual pointer value shall not be
   --  used).

   --  A pragma Annotate for container aggregates has the following form:
   --    pragma Annotate (GNATprove, Container_Aggegates, Id, Entity => E);

   --  where
   --    GNATprove           is a fixed identifier
   --    Container_Aggegates is a fixed identifier
   --    Id                  is a string and can have several values to
   --                        annotate different kinds of container types and
   --                        functions.
   --    E                   is either a type with an Aggregate aspect or
   --                        a function declared in the immediate scope of
   --                        such a type.

   --  See the Aggregate_Annotation type for additional information of the
   --  different kinds of container types and their associated functions.

   --  A pragma Annotate for a handler has the following form:
   --    pragma Annotate (GNATprove, Handler, Entity => E);

   --  where
   --    GNATprove           is a fixed identifier
   --    Handler             is a fixed identifier
   --    E                   is an access-to-subprogram type.

   --  The access-to-subprogram type E shall be library level and shall not
   --  have a precondition nor a postcondition.

   --  A pragma Annotate to hide or disclose information has one of the
   --  following forms:
   --    pragma Annotate (GNATprove, Hide_Info,   "Info_Kind"[, Entity => E]);
   --    pragma Annotate (GNATprove, Unhide_Info, "Info_Kind"[, Entity => E]);

   --  where
   --    GNATprove                 is a fixed identifier
   --    Hide_Info and Unhide_Info are fixed identifiers
   --    Info_Kind                 is a string that can be either Package_Body,
   --                              Private_Part or Expression_Function_Body for
   --                              now.
   --    E                         is the entity whose information should be
   --                              hidden or disclosed. It is mandatory for
   --                              Expression_Function_Body, can be omitted for
   --                              Package_Body and cannot be supplied for
   --                              Private_Part.

   --  The annotation for package bodies and private part are not context
   --  dependent. They should be located either on the package body or at the
   --  top of the package body or private part.
   --  For expression function bodies, the location of the pragma gives the
   --  verification context on which information should be hidden or disclosed.
   --  It can only occur at the beginning of a package, subprogram, or entry
   --  body or right after a package, subprogram, or entry body or
   --  specification. The information is then hidden or disclosed (if it is
   --  hidden by default) for the verification of the package, subprogram, or
   --  entry.

   --  A pragma Annotate for private types with mutable IN parameters has the
   --  following form:
   --    pragma Annotate (GNATprove, Mutable_IN_Parameters, Entity => E);

   --  where
   --    GNATprove               is a fixed identifier
   --    Mutable_IN_Parameters   is a fixed identifier
   --    E                       is a private type.

   --  The private type E shall be either a simple private type or ultimately
   --  an access-to-variable type. It should be located directly after an
   --  entry or a subprogram with side effects.

   --  A pragma Annotate for predefined equality of private types can be
   --  applied either on a type or a constant. On a type, it has the following
   --  form:
   --    pragma Annotate
   --        (GNATprove, Predefined_Equality, Kind, Entity => E);

   --  where
   --    GNATprove           is a fixed identifier
   --    Predefined_Equality is a fixed identifier
   --    Kind                can be either "Only_Null" or "No_Equality"
   --    E                   is a type entity

   --  and E shall be a private type whose full view is in a part annotated
   --  with SPARK_Mode => Off.

   --  When such an annotation is provided for a type E, the SPARK tool will
   --  translate uses of the predefined equality on values of type E in a
   --  specific way depending on the kind:
   --   * If Kind is "No_Equality" then it will disallow uses of the predefined
   --     equality on E.
   --   * If Kind is "Only_Null" then it will disallow uses of the predefined
   --     equality on E unless one of the operand is recognized statically as
   --     a null value, see below. In this case, the predefined equality will
   --     be handled as the logical equality instead.
   --
   --  On a constant, it has the following form:
   --    pragma Annotate
   --        (GNATprove, Predefined_Equality, "Null_Value", Entity => E);

   --  where
   --    GNATprove           is a fixed identifier
   --    Predefined_Equality is a fixed identifier
   --    E                   is a constant entity

   --  and E shall be a constant of a type annotated with predefined equality
   --  of kind "Only_Null".

   procedure Mark_Pragma_Annotate
     (N : Node_Id; Preceding : Node_Id; Consider_Next : Boolean)
   with Pre => Is_Pragma_Annotate_GNATprove (N) and Present (Preceding);
   --  Call this procedure to register a pragma Annotate. The "Preceding" node
   --  is the node in the tree to which this pragma refers to. If Consider_Next
   --  is true, "Preceding" must be part of a list, and the pragma will
   --  be considered to also apply to all "Next" declarations following
   --  "Preceding" which are not from source.

   function In_Delayed_Annotation return Boolean;
   --  Return True while performing delayed checks for pragma annotate

   procedure Do_Delayed_Checks_On_Pragma_Annotate;
   --  Some checks for Annotate pragmas or aspects might have been delayed
   --  because necessary entities were not marked yet. Finish the checking and
   --  possibly raise some remaining errors.

   procedure Pull_Entities_For_Annotate_Pragma
     (E                 : Entity_Id;
      Queue_For_Marking : not null access procedure (E : Entity_Id));
   --  After an entity E with an Annotate pragma has been marked, it might be
   --  necessary to pull other entities which are related. Call
   --  Queue_For_Marking on all such entities.

   subtype Check_Annotate_Kind is
     GNATprove_Annotation_Kind range False_Positive .. Intentional;

   type Annotated_Range (Present : Boolean := False) is record
      case Present is
         when True =>
            Kind    : Check_Annotate_Kind; --  the kind of pragma Annotate
            Pattern : String_Id;     --  the message pattern
            Reason  : String_Id;     --  the user-provided reason for hiding
            First   : Source_Ptr;    --  first source pointer
            Last    : Source_Ptr;    --  last source pointer
            Prgma   : Node_Id;       --  the pragma which this range belongs to

         when False =>
            null;
      end case;
   end record;

   function Decl_Starts_Pragma_Annotate_Range (N : Node_Id) return Boolean;
   --  When scanning a list of statements or declarations to decide the range
   --  of application of a pragma Annotate, some statements starts a new range
   --  for pragma to apply. If the declaration does not come from source, we
   --  consider it to be part of the preceding one as far as pragma Annotate
   --  is concerned. The exception to this rule are expression functions, and
   --  assertions which are rewritten by the front-end into pragma Check.

   procedure Check_Is_Annotated
     (Node  : Node_Id;
      Msg   : String;
      Check : Boolean;
      Info  : out Annotated_Range);
   --  For a given node and a message string, search if there is a pragma
   --  Annotate that applies to the message for this node. If so, set Found to
   --  True and fill in the Info record. Otherwise, set Found to False and
   --  leave Info uninitialized.

   --  This procedure also marks the corresponding pragma as covering a check.
   --  If Check is True, the pragma is marked as covering a failing check,
   --  otherwise it is marked as covering a proved check.

   procedure Generate_Useless_Pragma_Annotate_Warnings;
   --  Should be called when all messages have been generated. Generates a
   --  warning for all pragma Annotate which do not correspond to a check,
   --  or which covers only proved checks.

   type Iterable_Kind is (Model, Contains);

   type Iterable_Annotation is record
      Kind   : Iterable_Kind;   --  the kind of Annotate Iterable_For_Proof
      Entity : Entity_Id;       --  the entity of the corresponding function
   end record;

   function Retrieve_Inline_Annotation (E : Entity_Id) return Node_Id;
   --  If a pragma Annotate Inline_For_Proof applies to E then returns the
   --  Ada expression that should be used instead of E.

   function Find_Inline_Pragma (E : Entity_Id) return Node_Id
   with
     Pre  =>
       Present (Retrieve_Inline_Annotation (E))
       or else Has_Logical_Eq_Annotation (E),
     Post => Is_Pragma_Annotate_GNATprove (Find_Inline_Pragma'Result);
   --  If a pragma Annotate Inline_For_Proof or Logical_Equal applies to E then
   --  returns this pragma. This is used to get better location when checking
   --  these pragmas.

   procedure Retrieve_Iterable_Annotation
     (Container_Type : Entity_Id;
      Found          : out Boolean;
      Info           : out Iterable_Annotation);
   --  For a given container type with Iterable aspect, search if there is a
   --  pragma Annotate Iterable_For_Proof that applies to type. If so, set
   --  Found to True and fill in the Info record. Otherwise, set Found to False
   --  and leave Info uninitialized.

   function Has_Logical_Eq_Annotation (E : Entity_Id) return Boolean;
   --  Return True if a pragma Annotate Logical_Equal applies to entity E

   function Has_No_Bitwise_Operations_Annotation
     (E : Entity_Id) return Boolean;
   --  Return True if a pragma Annotate No_Bitwise_Operations applies to the
   --  type E.

   procedure Set_Has_No_Bitwise_Operations_Annotation (E : Entity_Id);
   --  Register entity E has having the No_Bitwise_Operations annotation,
   --  either directly or inherited through a parent type (for derived types)
   --  or base type (for subtypes). Integer types with Unsigned_Base_Range
   --  must also be registered. They are modular types internally but should be
   --  treated almost as signed integers.

   function Has_No_Wrap_Around_Annotation (E : Entity_Id) return Boolean
   with Pre => Is_Type (E);
   --  Return True if a pragma Annotate No_Wrap_Around applies to the type E

   procedure Set_Has_No_Wrap_Around_Annotation (E : Entity_Id);
   --  Register entity E has having the No_Wrap_Around annotation, either
   --  directly or inherited through a parent type (for derived types) or base
   --  type (for subtypes). Integer types with Unsigned_Base_Range
   --  must not be registered. Despite the similitude with No_Wrap_Around,
   --  they are affected by overflow mode, which force distinct handling.

   function Has_At_End_Borrow_Annotation (E : Entity_Id) return Boolean;
   --  Return True if the function E is a function annotated with at_end_borrow

   procedure Infer_Inline_Annotation (E : E_Function_Id);
   --  Decide whether pragma Inline_For_Proof can be inferred for E

   function Is_Pragma_Annotate_Automatic_Instantiation
     (N : Node_Id; P : Entity_Id := Empty) return Boolean
   with Pre => Is_Pragma_Annotate_GNATprove (N);
   --  Return True if N is a pragma Annotate (GNATprove,
   --  Automatic_Instantiation, P). If P is Empty, accept any procedure entity.

   function Has_Skip_Proof_Annotation (E : Entity_Id) return Boolean;
   --  True if E or an enclosing entity has pragma Annotate(GNATProve,
   --  Skip_Proof) or pragma Annotate (GNATProve, Skip_Flow_And_Proof).

   function Has_Skip_Flow_And_Proof_Annotation (E : Entity_Id) return Boolean;
   --  True if E or an enclosing entity has pragma Annotate (GNATprove,
   --  Skip_Flow_And_Proof).

   Skipped_Flow_And_Proof : Node_Sets.Set;
   Skipped_Proof          : Node_Sets.Set;
   --  These sets contain all entities for which flow or proof (or both) was
   --  actually skipped.

   function Has_Own_Ownership_Annotation (E : Entity_Id) return Boolean
   with Pre => Is_Type (E);
   --  Return True if E is annotated with ownership

   function Has_Ownership_Annotation (E : Entity_Id) return Boolean
   with Pre => Is_Type (E);
   --  Return True if E has a possibly inherited ownership annotation and its
   --  full view is not in SPARK.

   function Needs_Ownership_Check (E : Entity_Id) return Boolean
   with Pre => Is_Type (E);
   --  Return True if E is annotated with ownership, it needs reclamation, and
   --  its full view is in SPARK.

   function Needs_Reclamation (E : Entity_Id) return Boolean
   with Pre => Is_Type (E) and then Has_Ownership_Annotation (E);
   --  Return True if E needs checks to ensure that the memory is reclaimed

   type Reclamation_Kind is (Reclaimed_Value, Is_Reclaimed, Needs_Reclamation);

   procedure Get_Reclamation_Entity
     (E                  : Entity_Id;
      Reclamation_Entity : out Entity_Id;
      Kind               : out Reclamation_Kind;
      For_Check          : Boolean := False)
   with
     Pre =>
       Is_Type (E)
       and then
         (if For_Check
          then Needs_Ownership_Check (E)
          else Has_Ownership_Annotation (E) and then Needs_Reclamation (E));
   --  Retrieve the check function or constant for a type which needs
   --  reclamation if any. If For_Check is True, return the confirming
   --  annotation. Otherwise confirming annotations are ignored.

   function Get_Reclamation_Entity (E : Entity_Id) return Entity_Id
   with
     Pre =>
       Is_Type (E)
       and then Has_Ownership_Annotation (E)
       and then Needs_Reclamation (E);
   --  Same as above but only returns the check function

   procedure Infer_Ownership_Annotation (E : Type_Kind_Id);
   --  Infer ownership annotation for E. This is used when abstracting away
   --  unused record components. E should be a root retysp here.

   function Has_Own_Predefined_Eq_Annotation (E : Entity_Id) return Boolean
   with Pre => Is_Type (E);
   --  Return True if E is annotated with predefined equality

   function Has_Predefined_Eq_Annotation (E : Entity_Id) return Boolean
   with Pre => Is_Type (E);
   --  Return True if E has a potentially inherited predefined equality
   --  annotation and its full view is not in SPARK.

   type Predefined_Eq_Kind is (Only_Null, No_Equality);

   function Get_Predefined_Eq_Kind (E : Entity_Id) return Predefined_Eq_Kind
   with Pre => Is_Type (E) and then Has_Predefined_Eq_Annotation (E);
   --  Return expected handling for the predefined equality on E

   function Get_Null_Value (E : Entity_Id) return Entity_Id
   with
     Pre =>
       Is_Type (E)
       and then Has_Predefined_Eq_Annotation (E)
       and then Get_Predefined_Eq_Kind (E) = Only_Null;
   --  Return the null value for private types whose predefined equality is
   --  only allowed on null values.

   function Has_Automatic_Instantiation_Annotation
     (E : Entity_Id) return Boolean;
   --  Return True if a pragma Annotate Automatic_Instantiation applies to the
   --  procedure E.

   function Retrieve_Automatic_Instantiation_Annotation
     (E : Entity_Id) return Entity_Id
   with Pre => Has_Automatic_Instantiation_Annotation (E);
   --  If a pragma Annotate Automatic_Instantiation applies to E then return
   --  the function to which E is associated.

   function Has_Higher_Order_Specialization_Annotation
     (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in E_Function | E_Procedure;
   --  Return True if a pragma Annotate Higher_Order_Specialization applies to
   --  the function E.

   function Get_Lemmas_To_Specialize (E : Entity_Id) return Node_Sets.Set
   with
     Pre =>
       Ekind (E) = E_Function
       and then Has_Higher_Order_Specialization_Annotation (E);
   --  Return a set of lemmas that should be specialized along with the
   --  function E.

   function Retrieve_Parameter_Specialization
     (E : Entity_Id) return Node_Maps.Map
   with
     Pre =>
       Ekind (E) = E_Procedure
       and then Has_Automatic_Instantiation_Annotation (E)
       and then
         Has_Higher_Order_Specialization_Annotation
           (Retrieve_Automatic_Instantiation_Annotation (E));
   --  Return a mapping from the formal parameters of the function associated
   --  to a lemma procedure E to the formals of E. It should be used to
   --  construct a specialization of E from a specialization of the function.

   type Aggr_Annotation_Kind is (Sets, Maps, Seqs, Model);
   --  Different kinds for aggregate annotations. Sets, Maps, and Seqs are
   --  for predefined aggregate kinds, respectively for aggregates for:
   --  * sets: unordered, equivalent elements are merged;
   --  * maps: unordered mappings from keys to elements, unicity of keys is
   --    enforced;
   --  * sequences: ordered, indexed by integer types (big or signed).
   --  Model can be used to specify aggregates by providing a model function
   --  to another type with compatible aggregates.

   type Aggregate_Annotation (Kind : Aggr_Annotation_Kind := Sets) is record
      Annotate_Node  : Node_Id;
      Empty_Function : Entity_Id;
      Add_Procedure  : Entity_Id;
      Use_Named      : Boolean;
      Spec_Capacity  : Entity_Id := Empty;
      Capacity       : Entity_Id := Empty;

      case Kind is
         when Sets | Maps | Seqs =>
            Element_Type : Entity_Id;

            case Kind is
               when Sets =>
                  Contains            : Entity_Id := Empty;
                  Equivalent_Elements : Entity_Id := Empty;
                  Sets_Length         : Entity_Id := Empty;

               when Maps =>
                  Key_Type        : Entity_Id;
                  Has_Key         : Entity_Id := Empty;
                  Default_Item    : Entity_Id := Empty;
                  Equivalent_Keys : Entity_Id := Empty;
                  Maps_Get        : Entity_Id := Empty;
                  Maps_Length     : Entity_Id := Empty;

               when Seqs =>
                  Index_Type : Entity_Id := Empty;
                  Seqs_Get   : Entity_Id := Empty;
                  First      : Entity_Id := Empty;
                  Last       : Entity_Id := Empty;

               when others =>
                  null;
            end case;

         when Model =>
            Model_Type : Entity_Id := Empty;
            Model      : Entity_Id := Empty;
      end case;
   end record;
   --  Record used to store the functions associated to a type with aggregates.
   --  Predefined set aggregates are defined by a Contains and an
   --  Equivalent_Elements functions. An additional Length function can be
   --  supplied if the cardinality is of interest.
   --  Predefined map aggregates come in two flavors, either partial maps with
   --  an Has_Key function or total maps with a default item. In addition, all
   --  maps need to provide both an Equivalent_Keys and a Get functions, and
   --  partial maps can provide a Length function if the cardinality is of
   --  interest.
   --  Predefined sequence aggregates are defined by a Get, a First, and a Last
   --  function.
   --  Model aggregates need at least Model function.
   --  All kinds of aggregates can be supplied with an additional Capacity
   --  function. It shall take the container as a parameter iff the empty
   --  function takes the capacity as a parameter. Spec_Capacity holds the
   --  type of the Capacity parameter of the empty function in this case.

   function Has_Aggregate_Annotation (E : Type_Kind_Id) return Boolean;

   function Get_Aggregate_Annotation
     (E : Type_Kind_Id) return Aggregate_Annotation
   with Pre => Has_Aggregate_Annotation (E);

   function Has_Handler_Annotation (E : Type_Kind_Id) return Boolean;

   type Hide_Annotation_Kind is
     (Hide_Expr_Fun, Unhide_Expr_Fun, Unhide_Package_Body);

   package Node_To_Hide_Annotation_Kind_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Node_Id,
        Element_Type    => Hide_Annotation_Kind,
        Hash            => Node_Hash,
        Equivalent_Keys => "=");

   function Get_Hide_Annotations
     (E : Entity_Id) return Node_To_Hide_Annotation_Kind_Maps.Map;
   --  Return all the hide or unhide annotations applying to E

   function Expr_Fun_Might_Be_Hidden (E : Entity_Id) return Boolean;
   --  Return True if the body of an expression function E might be hidden

   function Expr_Fun_Hidden_By_Default (E : Entity_Id) return Boolean;
   --  Return True if the body of an expression function E is hidden by default

   function Has_Visible_Package_Body (E : Entity_Id) return Boolean;
   --  Return True if the body of a nested package E is unhidden

   function Has_Mutable_In_Param_Annotation (E : Entity_Id) return Boolean
   with Pre => Ekind (E) = E_In_Parameter;
   --  Return True if E is a IN parameter annotated as mutable

   function Has_Hidden_Private_Part (E : Entity_Id) return Boolean;
   --  Return True if the private of the package E is hidden

end SPARK_Definition.Annotate;
