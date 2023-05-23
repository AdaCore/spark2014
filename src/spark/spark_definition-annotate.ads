------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              S P A R K _ D E F I N I T I O N - A N N O T A T E           --
--                                                                          --
--                                  S p e c                                 --
--                                                                          --
--                     Copyright (C) 2011-2023, AdaCore                     --
--              Copyright (C) 2014-2023, Capgemini Engineering              --
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

with Atree;       use Atree;
with Einfo.Utils; use Einfo.Utils;
with SPARK_Util;  use SPARK_Util;

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

   --  This package also stores uses of pragma Annotate for Iterable_For_Proof
   --  and Inline_For_Proof. This uses are not documented as they are provided
   --  for internal use only.

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

   --  A pragma Annotate for termination has the following form:
   --    pragma Annotate (GNATprove, Always_Return, Entity => E);

   --  where
   --    GNATprove           is a fixed identifier
   --    Always_Return       is a fixed identifier
   --    E                   is a subprogram or a package entity

   --  When such an annotation is provided for a subprogram E, it is assumed to
   --  terminate as far as proof is concerned. If it is provided for a package,
   --  then all the subprograms declared in this package are assumed to
   --  terminate.

   --  A pragma Annotate for ownership can be applied either on a type or a
   --  function. On a type, it has the following form:
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

   procedure Mark_Pragma_Annotate
     (N             : Node_Id;
      Preceding     : Node_Id;
      Consider_Next : Boolean)
     with Pre => Is_Pragma_Annotate_GNATprove (N) and Present (Preceding);
   --  Call this procedure to register a pragma Annotate. The "Preceding" node
   --  is the node in the tree to which this pragma refers to. If Consider_Next
   --  is true, "Preceding" must be part of a list, and the pragma will
   --  be considered to also apply to all "Next" declarations following
   --  "Preceding" which are not from source.

   procedure Do_Delayed_Checks_On_Pragma_Annotate;
   --  Some checks for Annotate pragmas or aspects might have been delayed
   --  because necessary entities were not marked yet. Finish the checking and
   --  possibly raise some remaining errors.

   type Annotate_Kind is (Intentional, False_Positive);

   type Annotated_Range is record
      Kind    : Annotate_Kind;       --  the kind of pragma Annotate
      Pattern : String_Id;           --  the message pattern
      Reason  : String_Id;           --  the user-provided reason for hiding
      First   : Source_Ptr;          --  first source pointer
      Last    : Source_Ptr;          --  last source pointer
      Prgma   : Node_Id;             --  the pragma which this range belongs to
   end record;

   function Decl_Starts_Pragma_Annotate_Range (N : Node_Id) return Boolean is
     (Comes_From_Source (N)
      or else (Is_Rewrite_Substitution (N)
               and then Comes_From_Source (Original_Node (N))));
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
      Found : out Boolean;
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

   function Find_Inline_Pragma (E : Entity_Id) return Node_Id with
     Pre  => Present (Retrieve_Inline_Annotation (E))
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

   function Has_Might_Not_Return_Annotation (E : Entity_Id) return Boolean
   with Pre => Ekind (E) in Entry_Kind
                          | E_Function
                          | E_Package
                          | E_Procedure
                          | E_Generic_Procedure
                          | E_Task_Type
                          | E_Subprogram_Type,
        Post => (if Has_Might_Not_Return_Annotation'Result
                 then Ekind (E) in E_Procedure | E_Generic_Procedure);
   --  Return True if a pragma Annotate Might_Not_Return applies to entity E

   function Has_No_Wrap_Around_Annotation (E : Entity_Id) return Boolean
   with Pre => Is_Type (E);
   --  Return True if a pragma Annotate No_Wrap_Around applies to the type E

   procedure Set_Has_No_Wrap_Around_Annotation (E : Entity_Id);
   --  Register entity E has having the No_Wrap_Around annotation, either
   --  directly or inherited through a parent type.

   function To_String (Kind : Annotate_Kind) return String is
     (case Kind is
         when False_Positive => "false positive",
         when Intentional    => "intentional");
   --  Return the string representation of the supplied annotation

   function Has_Always_Return_Annotation (E : Entity_Id) return Boolean;
   --  Return True if a pragma Annotate Always_Return applies to the subprogram
   --  E.

   function Has_At_End_Borrow_Annotation (E : Entity_Id) return Boolean;
   --  Return True if the function E is a function annotated with at_end_borrow

   procedure Infer_Inline_Annotation (E : E_Function_Id);
   --  Decide whether pragma Inline_For_Proof can be inferred for E

   function Is_Pragma_Annotate_Automatic_Instantiation
     (N : Node_Id;
      P : Entity_Id := Empty) return Boolean
   with Pre => Is_Pragma_Annotate_GNATprove (N);
   --  Return True if N is a pragma Annotate (GNATprove,
   --  Automatic_Instantiation, P). If P is Empty, accept any procedure entity.

   function Has_Ownership_Annotation (E : Entity_Id) return Boolean
     with Pre => Is_Type (E);
   --  Return True if E is annotated with ownership

   function Needs_Reclamation (E : Entity_Id) return Boolean
     with Pre => Is_Type (E) and then Has_Ownership_Annotation (E);
   --  Return True if E needs checks to ensure that the memory is reclaimed

   procedure Get_Reclamation_Check_Function
     (E              : Entity_Id;
      Check_Function : out Entity_Id;
      Reclaimed      : out Boolean)
   with Pre => Is_Type (E)
     and then Has_Ownership_Annotation (E)
     and then Needs_Reclamation (E);
   --  Retrieve the check function for a type which needs reclamation if any

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
   with Pre => Ekind (E) = E_Function
     and then Has_Higher_Order_Specialization_Annotation (E);
   --  Return a set of lemmas that should be specialized along with the
   --  function E.

   function Retrieve_Parameter_Specialization
     (E : Entity_Id) return Node_Maps.Map
   with Pre => Ekind (E) = E_Procedure
     and then Has_Automatic_Instantiation_Annotation (E)
     and then Has_Higher_Order_Specialization_Annotation
       (Retrieve_Automatic_Instantiation_Annotation (E));
   --  Return a mapping from the formal parameters of the function associated
   --  to a lemma procedure E to the formals of E. It should be used to
   --  construct a specialization of E from a specialization of the function.

end SPARK_Definition.Annotate;
