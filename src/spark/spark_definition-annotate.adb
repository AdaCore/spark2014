------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              S P A R K _ D E F I N I T I O N - A N N O T A T E           --
--                                                                          --
--                                  B o d y                                 --
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

with Ada.Characters.Handling;     use Ada.Characters.Handling;
with Ada.Containers.Doubly_Linked_Lists;
with Ada.Containers.Ordered_Maps;
with Ada.Strings.Unbounded;       use Ada.Strings.Unbounded;
with Aspects;                     use Aspects;
with Checked_Types;               use Checked_Types;
with Common_Containers;
with Errout;
with Erroutc;
with Errout_Wrapper;              use Errout_Wrapper;
with Flow_Refinement;             use Flow_Refinement;
with Flow_Types;                  use Flow_Types;
with Flow_Utility;                use Flow_Utility;
with Gnat2Why_Args;
with Namet;                       use Namet;
with Nlists;                      use Nlists;
with Opt;
with Rtsfind;                     use Rtsfind;
with Sem_Aux;                     use Sem_Aux;
with Sem_Ch12;
with Sem_Ch13;                    use Sem_Ch13;
with Sem_Prag;                    use Sem_Prag;
with Sinfo.Utils;                 use Sinfo.Utils;
with Sinput;                      use Sinput;
with Snames;                      use Snames;
with SPARK_Definition.Violations; use SPARK_Definition.Violations;
with SPARK_Util.Subprograms;      use SPARK_Util.Subprograms;
with SPARK_Util.Types;            use SPARK_Util.Types;
with Stand;                       use Stand;
with Stringt;                     use Stringt;
with String_Utils;                use String_Utils;
with VC_Kinds;                    use VC_Kinds;

package body SPARK_Definition.Annotate is

   package Annot_Ranges is new
     Ada.Containers.Doubly_Linked_Lists (Element_Type => Annotated_Range);
   --  ??? why not use Ordered_Sets here?

   function "<" (L, R : Annotated_Range) return Boolean;
   --  Ordering relation on annotated ranges; used only for assertions

   package Annot_Range_Sorting is new Annot_Ranges.Generic_Sorting;
   --  Sorting of annotated ranges; used only to assert that data in the
   --  container is indeed sorted.

   package Iterable_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Node_Id,
        Element_Type    => Iterable_Annotation,
        Hash            => Common_Containers.Node_Hash,
        Equivalent_Keys => "=");

   Pragma_Seen : Common_Containers.Hashed_Node_Sets.Set :=
     Common_Containers.Hashed_Node_Sets.Empty_Set;
   --  This set contains all pragma annotate nodes that have been processed.
   --  It's purpose is to avoid processing a pragma twice. This set is not
   --  used directly to produce output, so we can use a hashed set.

   Pragma_Set : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  After marking, this set contains all pragma Annotate nodes that suppress
   --  check messages. They are removed from the set one by one when messages
   --  which are covered by these pragmas are encountered. At the end, only
   --  pragmas which don't cover a message will be in this set.

   Proved_Pragma : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  This set contains all pragma Annotate Nodes which correspond only to a
   --  proved check.

   Annotations : Annot_Ranges.List := Annot_Ranges.Empty_List;
   --  Sorted ranges

   package Node_To_Aggregates_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Node_Id,
        Element_Type    => Aggregate_Annotation,
        Hash            => Node_Hash,
        Equivalent_Keys => "=");

   Aggregate_Annotations : Node_To_Aggregates_Maps.Map;
   --  Stores type entities with a pragma Annotate
   --  (GNATprove, Container_Aggregate, ..., E) and map them to their
   --  related entities.

   At_End_Borrow_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores function entities with a pragma Annotate
   --  (GNATprove, At_End_Borrow, E).

   Automatic_Instantiation_Annotations : Common_Containers.Node_Maps.Map :=
     Common_Containers.Node_Maps.Empty_Map;
   --  Maps lemma procedures annotated with Automatic_Instantiation to their
   --  associated function.

   Delayed_Checks_For_Aggregates : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Set of types annotated with Container_Aggregates that need to be checked

   type Delayed_Aggregate_Function_Key is record
      Enclosing_List      : List_Id;
      Base_Component_Type : Entity_Id;
   end record;
   --  Keys to store delayed functions annotated with container aggregates are
   --  the enclosing list of declarations and the base type of the element or
   --  key type. They will be used to find delayed functions from the
   --  corresponding container type (in the same list of declarations and with
   --  compatible components).

   function "<" (X, Y : Delayed_Aggregate_Function_Key) return Boolean
   is (X.Enclosing_List < Y.Enclosing_List
       or else
         (X.Enclosing_List = Y.Enclosing_List
          and then X.Base_Component_Type < Y.Base_Component_Type));
   package Delayed_Aggregate_Function_Maps is new
     Ada.Containers.Ordered_Maps
       (Key_Type     => Delayed_Aggregate_Function_Key,
        Element_Type => Entity_Id);

   Delayed_Default_Item        : Delayed_Aggregate_Function_Maps.Map;
   Delayed_Equivalent_Elements : Delayed_Aggregate_Function_Maps.Map;
   Delayed_Equivalent_Keys     : Delayed_Aggregate_Function_Maps.Map;
   Delayed_First               : Delayed_Aggregate_Function_Maps.Map;
   Delayed_Capacity            : Delayed_Aggregate_Function_Maps.Map;
   --  Delayed function entities for aggregates

   Delayed_Checks_For_Lemmas : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Set of lemmas with automatic instantiation that need to be checked

   Delayed_HO_Specialization_Checks : Common_Containers.Node_Maps.Map :=
     Common_Containers.Node_Maps.Empty_Map;
   --  Maps calls to functions which were not marked yet but should be
   --  annotated with Higher_Order_Specialization to the node on which the
   --  checks shall be emited.

   type Node_Pair is record
      First : Node_Id;
      Snd   : Node_Id;
   end record;

   package Node_To_Node_Pairs is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Node_Id,
        Element_Type    => Node_Pair,
        Hash            => Node_Hash,
        Equivalent_Keys => "=");
   --  Maps of nodes to pairs of nodes

   Delayed_Hide_Compatibility_Checks : Node_To_Node_Pairs.Map :=
     Node_To_Node_Pairs.Empty_Map;
   --  Map Hide or Unhide annotations that should be checked for compatibility
   --  with the default to their scope and their entity.

   Higher_Order_Spec_Annotations : Common_Containers.Node_Graphs.Map :=
     Common_Containers.Node_Graphs.Empty_Map;
   --  Stores function entities with a pragma Annotate
   --  (GNATprove, Higher_Order_Specialization, E). They are mapped to a
   --  (possibly empty) set of  lemmas that should be automatically
   --  instantiated when the function is specialized.

   package Node_To_Node_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Node_Id,
        Element_Type    => Node_Maps.Map,
        Hash            => Node_Hash,
        Equivalent_Keys => "=",
        "="             => Node_Maps."=");
   --  Maps of nodes to maps of nodes to nodes

   Handler_Annotations : Node_Sets.Set;
   --  Stores all the access-to-subprogram types E with a pragma Annotate
   --  (GNATprove, Handler, E).

   Higher_Order_Lemma_Specializations : Node_To_Node_Maps.Map :=
     Node_To_Node_Maps.Empty_Map;
   --  Maps lemma procedures to the mapping that should be used to construct
   --  their specialization from their associated function specialization.

   Inline_Annotations          : Common_Containers.Node_Maps.Map :=
     Common_Containers.Node_Maps.Empty_Map;
   --  Maps all the function entities E with a pragma Annotate
   --  (GNATprove, Inline_For_Proof, E) to their expression.
   Inferred_Inline_Annotations : Common_Containers.Node_Maps.Map :=
     Common_Containers.Node_Maps.Empty_Map;
   --  Same as above but for annotations inferred by the tool

   Inline_Pragmas : Common_Containers.Node_Maps.Map :=
     Common_Containers.Node_Maps.Empty_Map;
   --  Maps all the function entities E with a pragma Annotate
   --  (GNATprove, Inline_For_Proof, E) to th pragma. This is used to get
   --  better location for checks for inline.

   Iterable_Annotations : Iterable_Maps.Map := Iterable_Maps.Empty_Map;
   --  A map from Iterable aspects to Iterable annotations

   Logical_Eq_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores all the function entities E with a pragma Annotate
   --  (GNATprove, Logical_Equal, E).

   Mutable_In_Params_Annotations : Common_Containers.Node_Graphs.Map :=
     Common_Containers.Node_Graphs.Empty_Map;
   --  Maps all subprogram entities followed by one or more pragmas Annotate
   --  (GNATprove, Mutable_In_Parameters, Ty) to a set containing all such
   --  types Ty.

   No_Bitwise_Operations_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores type entities with a pragma Annotate
   --  (GNATprove, No_Bitwise_Operations, E).

   No_Wrap_Around_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores type entities with a pragma Annotate
   --  (GNATprove, No_Wrap_Around, E).

   package Hide_Annotations_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Node_Id,
        Element_Type    => Node_To_Hide_Annotation_Kind_Maps.Map,
        Hash            => Node_Hash,
        Equivalent_Keys => "=",
        "="             => Node_To_Hide_Annotation_Kind_Maps."=");

   Hide_Or_Unhide_Annotations : Hide_Annotations_Maps.Map :=
     Hide_Annotations_Maps.Empty_Map;
   --  Map entities to the hide or unhide annotations that should be
   --  considered for its body.

   Potentially_Hidden_Entities : Node_To_Hide_Annotation_Kind_Maps.Map :=
     Node_To_Hide_Annotation_Kind_Maps.Empty_Map;
   --  Map potentially hidden entities to their default

   Potentially_Hidden_Private_Parts : Node_To_Bool_Maps.Map :=
     Node_To_Bool_Maps.Empty_Map;
   --  Map package entities to a boolean stating whether or not their private
   --  part is hidden.

   Skip_Proof_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores entities with pragma Annotate (GNATprove, Skip_Proof, E);

   Skip_Flow_And_Proof_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores entities with
   --    pragma Annotate (GNATprove, Skip_Flow_And_Proof, E);

   type Ownership_Annotation (Needs_Reclamation : Boolean := False) is record
      Confirming : Boolean;
      case Needs_Reclamation is
         when True =>
            Reclamation_Entity : Entity_Id := Empty;
            Reclaimed          : Reclamation_Kind := Reclaimed_Value;

         when False =>
            null;
      end case;
   end record;

   package Node_To_Ownership_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Node_Id,
        Element_Type    => Ownership_Annotation,
        Hash            => Common_Containers.Node_Hash,
        Equivalent_Keys => "=");

   Ownership_Annotations : Node_To_Ownership_Maps.Map :=
     Node_To_Ownership_Maps.Empty_Map;
   --  Maps all type entities E with a pragma Annotate
   --  (GNATprove, Ownership, [Needs_Reclamation,] E) to a record holding a
   --  boolean Needs_Reclamation set to True iff the type needs memory
   --  reclamation, a function entity Check_Function if a function was supplied
   --  to check whether or not objects of type E own a resource, and a boolean
   --  Reclaimed which is the value returned by the check function when called
   --  on an object which was reclaimed (to accomodate both Is_Reclaimed and
   --  Needs_Reclamation functions). Confirming is set to True if the full
   --  view of E is visible for the current analysis.

   type Predefined_Eq_Annotation (Kind : Predefined_Eq_Kind := No_Equality) is
   record
      Confirming : Boolean;
      case Kind is
         when Only_Null =>
            Null_Value : Entity_Id := Empty;

         when others =>
            null;
      end case;
   end record;

   package Node_To_Predefined_Eq_Maps is new
     Ada.Containers.Hashed_Maps
       (Key_Type        => Node_Id,
        Element_Type    => Predefined_Eq_Annotation,
        Hash            => Common_Containers.Node_Hash,
        Equivalent_Keys => "=");

   Predefined_Eq_Annotations : Node_To_Predefined_Eq_Maps.Map :=
     Node_To_Predefined_Eq_Maps.Empty_Map;
   --  Maps all type entities E with a pragma Annotate
   --  (GNATprove, Predefined_Equality, ..., E) to a record whose discriminant
   --  is an annotation kind. It can be either No_Equality if the predefined
   --  equality on E is entirely disallowed or Only_Null if it is still allowed
   --  if one of the operands is a special constant. In the second cased, an
   --  the component Null_Value stores the entity on which the predefined
   --  equality can be used. Confirming is set to True if the full view of E is
   --  visible for the current analysis.

   Delayed_Null_Values : Node_Lists.List;
   --  For confirming Predefined_Equality annotations, we need to check that
   --  the value of the constant is a null value. The check is delayed to be
   --  sure the full view is marked. All entities which have not be checked
   --  are stored in Delayed_Null_Values.

   procedure Insert_Annotate_Range
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      Range_Node      : Node_Id;
      Whole           : Boolean);
   --  Insert a certain range into the sorted vector of node ranges, with
   --  [prgma] as the corresponding pragma. The range is computed as follows.
   --  If [Whole] is true the entire range of the node is considered. If
   --  [Whole] is false, only the range First_Sloc (Range_Node) .. Pragma_Sloc
   --  is inserted.

   procedure Insert_Annotate_Range
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      First, Last     : Source_Ptr);
   --  Same as above, but take the node range in argument

   procedure Insert_With_Next
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      First_Node      : Node_Id;
      Skip            : Node_Id := Empty);
   --  Same as above, but also consider all nodes "next" after First_Node,
   --  until (and excluding) a node which comes from source. The Exclude
   --  argument can be used to skip a specific node.

   type Check_Justification (Present : Boolean := False) is record
      case Present is
         when False =>
            null;

         when True =>
            Kind    : Annotate_Kind;
            Pattern : String_Id;
            Reason  : String_Id;
      end case;
   end record;

   procedure Check_Pragma_Annotate_GNATprove
     (Prag : Node_Id; Result : out Check_Justification)
   with Pre => Is_Pragma_Annotate_GNATprove (Prag);
   --  Check validity of the pragma Annotate (GNATprove, ...). For annotations
   --  used to justify check messages, fill in the kind, pattern and reason of
   --  the pragma in Result. Result.Present is False if some syntax error
   --  has been detected, or if the pragma Annotate is not used for
   --  justification purposes.

   procedure Check_Annotate_Entity_Argument
     (Arg                 : Node_Id;
      Prag                : Node_Id;
      Prag_Name           : String;
      Continue            : out Boolean;
      Ignore_SPARK_Status : Boolean := False);
   --  Check that 'Arg' maps to an entity, and emit appropriate error message.
   --  If generic, also checks that the pragma is at a location that will be
   --  duplicated for instances.
   --  Use continue flag to determine if subsequent checks should be performed
   --  (continue if not generic, no error and entity in SPARK).
   --  If Ignore_SPARK_Status flag is set, do not check whether entity is
   --  in SPARK. In this case, the caller will determine the right entity
   --  for the test.

   type Annotate_Placement_Kind is
     (Placed_At_Specification,
      --  For subprogram/packages, placed at specification.
      Placed_At_Task_Specification,
      --  For task types, placed at specification.
      Placed_At_Declaration,
      --  For constants: placed at declaration (full or private view)
      Placed_At_Full_View, --  For type: placed at full view declaration
      Placed_At_Private_View); --  For type: placed at private view declaration

   function Annot_Applies_To
     (Prag : Node_Id; OK_Scope : Boolean := True; OK_Body : Boolean := True)
      return Opt_N_Entity_Id;
   --  Return the entity a location dependent annotation applies to, or
   --  Empty if none is found. It shall be a subprogram, entry, or package
   --  entity. The pragma can be localized either at the top inside the
   --  package, subprogram, or entry body, if OK_Scope is True, or just after
   --  the entity body, if OK_Body is True, or declaration. For now, it does
   --  not expect concurrent types nor generics.

   procedure Check_Aggregate_Annotation
     (Arg3_Exp : Node_Id; Arg4_Exp : Node_Id; Prag : Node_Id);
   --  Check validity of a pragma Annotate
   --  (GNATprove, Container_Aggregates, ???, E)
   --  and update the Aggregate_Annotations map.

   procedure Check_Annotate_Placement
     (Ent           : Entity_Id;
      Ent_Decl_Kind : Annotate_Placement_Kind;
      Prag          : Node_Id;
      Prag_Name     : String;
      Decl_Name     : String;
      Ok            : out Boolean);
   --  Check that 'Prag' is declared immediately after declaration of
   --  given entity, emitting appropriate error message.
   --  In case of package specification, the allowed range for the pragma
   --  is immediately after the 'is' of the package.
   --
   --  Pragmas converted from an aspect are considered well-placed by default.
   --  For entities with multiple views, we check that the aspect is attached
   --  to the expected view.

   procedure Check_Annotate_Placement
     (E : Entity_Id; Prag : Node_Id; Prag_Name : String; Ok : out Boolean)
   with
     Pre =>
       Ekind (E)
       in Subprogram_Kind
        | E_Constant
        | E_Package
        | Generic_Unit_Kind
        | E_Task_Type
        | Entry_Kind;
   --  Short form with common filling of arguments for case of entity
   --  being the pragma argument, in particular covering
   --  subprograms and packages.

   procedure Check_Automatic_Inst_And_HO_Specialization_Compatibility
     (Lemma : Subprogram_Kind_Id; Fun : Function_Kind_Id)
   with
     Pre =>
       Has_Automatic_Instantiation_Annotation (Lemma)
       and then Retrieve_Automatic_Instantiation_Annotation (Lemma) = Fun
       and then Has_Higher_Order_Specialization_Annotation (Fun);
   --  Check that lemmas associated to a function with higher order
   --  specialization can be specialized with the function. If it is not the
   --  case, emit a warning. Store compatible lemmas in the
   --  Higher_Order_Spec_Annotation map and their parameter associations in
   --  Higher_Order_Lemma_Specializations.

   procedure Check_Automatic_Instantiation_Annotation
     (Arg3_Exp : Node_Id; Prag : Node_Id)
   with Pre => Present (Arg3_Exp);
   --  Check validity of a pragma Annotate (GNATprove, Automatic_Instantiation,
   --  E) and insert it in the Automatic_Instantiation_Annotations map.

   procedure Check_At_End_Borrow_Annotation
     (Arg3_Exp : Node_Id; Prag : Node_Id)
   with Pre => Present (Arg3_Exp);
   --  Check validity of a pragma Annotate (GNATprove, At_End_Borrow, E) and
   --  insert it in the At_End_Borrow_Annotations map.

   procedure Check_Handler_Annotation (Arg3_Exp : Node_Id; Prag : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, Handler, E) and insert
   --  it in the Handler_Annotations set.

   procedure Check_Hide_Annotation
     (Aspect_Or_Pragma : String;
      Arg3_Exp         : Node_Id;
      Arg4_Exp         : Node_Id;
      Unhide           : Boolean;
      Prag             : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, Hide, ..., E) and insert
   --  it in the Hide_Or_Unhide_Annotations map. Also keep the
   --  Potentially_Hidden_Expr_Fun map up-to-date.

   procedure Check_Higher_Order_Specialization_Annotation
     (Arg3_Exp : Node_Id; Prag : Node_Id);
   --  Check validity of a pragma Annotate
   --  (GNATprove, Higher_Order_Specialization, E) and insert it in the
   --  Higher_Order_Spec_Annotations map.

   procedure Check_Inline_Annotation (Arg3_Exp : Node_Id; Prag : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, Inline_For_Proof, E)
   --  and insert it in the Inline_Annotations map.

   procedure Check_Iterable_Annotation
     (Arg3_Exp : Node_Id; Arg4_Exp : Node_Id; Prag : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, Iterate_For_Proof, E)
   --  and insert it in the Iterable_Annotations map.

   procedure Check_Logical_Equal_Annotation
     (Arg3_Exp : Node_Id; Prag : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, Logical_Equal, E)
   --  and insert it in the Logical_Eq_Annotations set.

   procedure Check_Mutable_In_Parameters_Annotation
     (Arg3_Exp : Node_Id; Prag : Node_Id);
   --  Check validity of a pragma Annotate
   --  (GNATprove, Mutable_In_Parameters, E) and fill the
   --  Mutable_In_Params_Annotations map.

   procedure Check_No_Bitwise_Operations_Annotation
     (Arg3_Exp : Node_Id; Prag : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, No_Bitwise_Operations,
   --  E) and insert it in the No_Bitwise_Operations_Annotations map.

   procedure Check_No_Wrap_Around_Annotation
     (Arg3_Exp : Node_Id; Prag : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, No_Wrap_Around, E)
   --  and insert it in the No_Wrap_Around_Annotations map.

   procedure Check_Ownership_Annotation
     (Aspect_Or_Pragma : String;
      Arg3_Exp         : Node_Id;
      Arg4_Exp         : Node_Id;
      Prag             : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, Ownership, ???, E)
   --  and update the Ownership_Annotations map.

   procedure Check_Predefined_Eq_Annotation
     (Aspect_Or_Pragma : String;
      Arg3_Exp         : Node_Id;
      Arg4_Exp         : Node_Id;
      Prag             : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, Predefined_Equality,
   --  ???, E) and update the Predefined_Eq_Annotations map.

   procedure Check_Skip_Annotations
     (Name : String; Arg3_Exp : Node_Id; Prag : Node_Id)
   with Pre => Name = "skip_proof" or else Name = "skip_flow_and_proof";
   --  Check validity of pragma Annotate (GNATprove, Skip_Proof, E) and
   --  pragma Annotate (GNATprove, Skip_Flow_And_Proof, E)

   procedure Do_Delayed_Checks_For_Aggregates (Typ : Entity_Id)
   with Pre => Has_Aggregate_Annotation (Typ);
   --  Make sure that all the necessary functions for container aggregates have
   --  been provided. Also fill the Aggregate_Annotations map to add function
   --  entities which do not take the container as a parameter.

   procedure Error_Msg_N_If
     (Msg           : String;
      N             : Node_Or_Entity_Id;
      Names         : Node_Lists.List := Node_Lists.Empty;
      Kind          : Msg_Severity := Error_Kind;
      Continuations : Message_Lists.List := Message_Lists.Empty);
   --  Wrapper for Error_Msg_N that conditionally emit message depending
   --  on phase.

   procedure Error_Msg_NE_If
     (Msg           : String;
      N             : Node_Or_Entity_Id;
      E             : Node_Or_Entity_Id;
      Kind          : Msg_Severity := Error_Kind;
      Continuations : Message_Lists.List := Message_Lists.Empty);
   --  Wrapper for Error_Msg_NE that conditionally emit message depending
   --  on phase.

   procedure Warning_Msg_N_If
     (Kind          : Misc_Warning_Kind;
      N             : Node_Or_Entity_Id;
      Names         : Node_Lists.List := Node_Lists.Empty;
      Continuations : Message_Lists.List := Message_Lists.Empty);

   function Find_Aggregate_Aspect (Typ : Type_Kind_Id) return Node_Id;
   --  Find the Aggregate aspect associated to Typ

   function Get_Container_Function_From_Pragma (N : Node_Id) return Entity_Id
   with Pre => Is_Pragma_Annotate_GNATprove (N);
   --  Return the function F such that N is a pragma Annotate
   --  (GNATprove, Container_Aggregates, ..., F) or a pragma Annotate
   --  (GNATprove, Iterable_For_Proof, ..., F).

   function Get_Ownership_Entity_From_Pragma
     (N : Node_Id; Ty : Entity_Id) return Entity_Id
   with Pre => Is_Pragma_Annotate_GNATprove (N);
   --  Return the function or constant F such that N is a pragma Annotate
   --  (GNATprove,  Ownership, ..., F) and F and Ty have the same root type if
   --  any.

   function Get_Predefined_Eq_Entity_From_Pragma
     (N : Node_Id; Ty : Entity_Id) return Entity_Id
   with Pre => Is_Pragma_Annotate_GNATprove (N);
   --  Return the constant C such that N is a pragma Annotate
   --  (GNATprove,  Ownership, ..., C) and C and Ty have the same root type if
   --  any.

   ---------
   -- "<" --
   ---------

   function "<" (L, R : Annotated_Range) return Boolean is
   begin
      return L.First < R.First;
   end "<";

   ----------------------
   -- Annot_Applies_To --
   ----------------------

   function Annot_Applies_To
     (Prag : Node_Id; OK_Scope : Boolean := True; OK_Body : Boolean := True)
      return Opt_N_Entity_Id
   is
      Cur : Node_Id := Prag;
   begin
      if not Is_List_Member (Prag) then
         return Empty;
      end if;

      loop
         Cur := Prev (Cur);
         exit when
           No (Cur)
           or else
             ((Comes_From_Source (Cur)
               or else Comes_From_Source (Original_Node (Cur)))
              and then Nkind (Cur) /= N_Pragma);
      end loop;

      if No (Cur) and then OK_Scope then
         Cur := Parent (Prag);
      end if;

      if Nkind (Cur)
         in N_Subprogram_Declaration
          | N_Entry_Declaration
          | N_Package_Declaration
      then
         return Unique_Defining_Entity (Cur);
      end if;

      if OK_Body
        and then
          Nkind (Cur) in N_Subprogram_Body | N_Entry_Body | N_Package_Body
      then
         return Unique_Defining_Entity (Cur);
      end if;

      return Empty;
   end Annot_Applies_To;

   --------------------------------
   -- Check_Aggregate_Annotation --
   --------------------------------

   procedure Check_Aggregate_Annotation
     (Arg3_Exp : Node_Id; Arg4_Exp : Node_Id; Prag : Node_Id)
   is

      function Is_Signed_Or_Big_Integer_Type (Ty : Entity_Id) return Boolean
      is (Is_Signed_Integer_Type (Ty)
          or else Is_RTE (Base_Type (Ty), RE_Big_Integer)
          or else Is_RTE (Base_Type (Ty), RO_SP_Big_Integer));

      From_Aspect : constant Boolean := From_Aspect_Specification (Prag);
      Prag_Name   : constant String := "Container_Aggregates";
      Ok          : Boolean;

   begin
      --  The 4th argument must be an entity

      Check_Annotate_Entity_Argument
        (Arg4_Exp, Prag, Prag_Name, Ok, Ignore_SPARK_Status => True);
      --  It would be fine to take SPARK status into account for type case,
      --  but not in function case.

      if not Ok then
         return;
      end if;

      --  The third argument must be a string literal

      if Nkind (Arg3_Exp) not in N_String_Literal then
         Mark_Incorrect_Use_Of_Annotation
           (Annot_String_Third_Argument,
            Arg3_Exp,
            Name        => Prag_Name,
            From_Aspect => From_Aspect);
         return;
      end if;

      declare
         Kind_Str : constant String :=
           To_Lower (To_String (Strval (Arg3_Exp)));
         Snd_Name : constant String := Standard_Ada_Case (Kind_Str);
         Ent      : constant Entity_Id := Entity (Arg4_Exp);
         Cont_Ty  : Entity_Id;

      begin
         if Ekind (Ent) in Type_Kind then
            declare
               Asp : constant Node_Id := Find_Aggregate_Aspect (Ent);

               Empty_Subp          : Node_Id := Empty;
               Add_Named_Subp      : Node_Id := Empty;
               Add_Unnamed_Subp    : Node_Id := Empty;
               New_Indexed_Subp    : Node_Id := Empty;
               Assign_Indexed_Subp : Node_Id := Empty;

               Annot : Aggregate_Annotation;
            begin

               if not In_SPARK (Ent) then
                  return;
               --  Annotation irrelevant if type not in SPARK

               end if;

               --  Check that the third parameter is an expected container kind

               if Kind_Str = "predefined_sets" then
                  Annot := (Kind => Sets, Use_Named => False, others => <>);
               elsif Kind_Str = "predefined_maps" then
                  Annot := (Kind => Maps, Use_Named => True, others => <>);
               elsif Kind_Str = "predefined_sequences" then
                  Annot := (Kind => Seqs, Use_Named => False, others => <>);
               elsif Kind_Str = "from_model" then
                  Annot := (Kind => Model, others => <>);
               else
                  Mark_Incorrect_Use_Of_Annotation
                    (Annot_Wrong_Third_Parameter,
                     Arg3_Exp,
                     Msg =>
                       "third parameter of "
                       & Annot_To_String
                           (Kind   => Annot_Wrong_Third_Parameter,
                            Format => Aspect_Or_Pragma (From_Aspect),
                            Name   => Prag_Name)
                       & " on a type shall be either Predefined_Sets, "
                       & "Predefined_Maps, Predefined_Sequences, or "
                       & "From_Model");
                  return;
               end if;

               Annot.Annotate_Node := Prag;

               if Nkind (Parent (Ent))
                  not in N_Private_Type_Declaration
                       | N_Private_Extension_Declaration
               then
                  Mark_Incorrect_Use_Of_Annotation
                    (Annot_Container_Aggregates_Private, Ent);
                  return;
               end if;

               --  The pragma should be placed on the initial type declaration

               Check_Annotate_Placement
                 (Ent,
                  Placed_At_Private_View,
                  Prag,
                  Prag_Name,
                  "initial declaration of " & Pretty_Source_Name (Ent),
                  Ok);

               if not Ok then
                  return;
               end if;

               --  Check that the entity has a container aggregate aspect

               if not Has_Aspect (Ent, Aspect_Aggregate) then
                  Mark_Incorrect_Use_Of_Annotation
                    (Annot_Container_Aggregates_No_Aggregate, Ent);
                  return;
               end if;

               Parse_Aspect_Aggregate
                 (N                   => Asp,
                  Empty_Subp          => Empty_Subp,
                  Add_Named_Subp      => Add_Named_Subp,
                  Add_Unnamed_Subp    => Add_Unnamed_Subp,
                  New_Indexed_Subp    => New_Indexed_Subp,
                  Assign_Indexed_Subp => Assign_Indexed_Subp);

               Annot.Empty_Function := Entity (Empty_Subp);
               pragma Assert (Ekind (Annot.Empty_Function) = E_Function);

               if Present (First_Formal (Annot.Empty_Function)) then
                  Annot.Spec_Capacity :=
                    Etype (First_Formal (Annot.Empty_Function));
                  pragma
                    Assert
                      (Number_Formals (Annot.Empty_Function) = 1
                       and then Is_Signed_Integer_Type (Annot.Spec_Capacity));
               end if;

               case Annot.Kind is
                  when Sets | Seqs =>
                     if No (Add_Unnamed_Subp) then
                        Mark_Incorrect_Use_Of_Annotation
                          (Annot_Container_Aggregates_Add,
                           Ent,
                           Snd_Name => Snd_Name,
                           Cont_Msg =>
                             Create ("procedure Add_Unnamed is expected"));
                        return;
                     else
                        Annot.Add_Procedure := Entity (Add_Unnamed_Subp);
                     end if;

                     declare
                        Cont_Formal : constant Entity_Id :=
                          First_Formal (Entity (Add_Unnamed_Subp));
                        Elem_Formal : constant Entity_Id :=
                          Next_Formal (Cont_Formal);
                     begin
                        Annot.Element_Type := Etype (Elem_Formal);
                     end;

                  when Maps        =>
                     if No (Add_Named_Subp) then
                        Mark_Incorrect_Use_Of_Annotation
                          (Annot_Container_Aggregates_Add,
                           Ent,
                           Snd_Name => Snd_Name,
                           Cont_Msg =>
                             Create ("procedure Add_Named is expected"));
                        return;
                     else
                        Annot.Add_Procedure := Entity (Add_Named_Subp);
                     end if;

                     declare
                        Cont_Formal : constant Entity_Id :=
                          First_Formal (Entity (Add_Named_Subp));
                        Key_Formal  : constant Entity_Id :=
                          Next_Formal (Cont_Formal);
                        Elem_Formal : constant Entity_Id :=
                          Next_Formal (Key_Formal);
                     begin
                        Annot.Key_Type := Etype (Key_Formal);
                        Annot.Element_Type := Etype (Elem_Formal);
                     end;

                  when Model       =>
                     if No (Add_Named_Subp) and then No (Add_Unnamed_Subp) then
                        Mark_Incorrect_Use_Of_Annotation
                          (Annot_Container_Aggregates_Add,
                           Ent,
                           Cont_Msg =>
                             Create
                               ("procedure Add_Named or Add_Unnamed is "
                                & "expected"));
                        return;
                     elsif Present (Add_Named_Subp) then
                        Annot.Add_Procedure := Entity (Add_Named_Subp);
                        Annot.Use_Named := True;
                     else
                        Annot.Add_Procedure := Entity (Add_Unnamed_Subp);
                        Annot.Use_Named := False;
                     end if;
               end case;

               --  Reject containers containing access-to-variable types as
               --  Add could modify its IN parameters.

               if (Annot.Kind = Maps
                   and then Is_Access_Object_Type (Annot.Key_Type)
                   and then not Is_Access_Constant (Annot.Key_Type))
                 or else
                   (Annot.Kind /= Model
                    and then Is_Access_Object_Type (Annot.Element_Type)
                    and then not Is_Access_Constant (Annot.Element_Type))
               then
                  Mark_Incorrect_Use_Of_Annotation
                    (Annot_Container_Aggregates_Add_Access_Param, Ent);
               end if;

               declare
                  Inserted : Boolean;
                  Position : Node_To_Aggregates_Maps.Cursor;
               begin
                  Aggregate_Annotations.Insert
                    (Base_Retysp (Ent), Annot, Position, Inserted);

                  if not Inserted then
                     Mark_Incorrect_Use_Of_Annotation
                       (Annot_Duplicated_Annotation,
                        Prag,
                        Name  => Prag_Name,
                        Names => [Ent]);
                  else
                     Delayed_Checks_For_Aggregates.Insert (Base_Retysp (Ent));
                  end if;
               end;
            end;

         elsif Ekind (Ent) = E_Function then

            --  First check that the third parameter is a valid kind

            if Kind_Str
               not in "equivalent_elements"
                    | "equivalent_keys"
                    | "capacity"
                    | "contains"
                    | "has_key"
                    | "default_item"
                    | "get"
                    | "length"
                    | "first"
                    | "last"
                    | "model"
            then
               Mark_Incorrect_Use_Of_Annotation
                 (Annot_Wrong_Third_Parameter,
                  Arg3_Exp,
                  From_Aspect => From_Aspect,
                  Name        => Prag_Name);
               return;
            end if;

            --  Common checks to all aggregate functions

            Check_Annotate_Placement
              (Ent,
               Placed_At_Specification,
               Prag,
               Prag_Name,
               "specification of function " & Pretty_Source_Name (Ent),
               Ok);

            if not Ok then
               return;
            end if;

            if Is_Function_With_Side_Effects (Ent) then
               Mark_Incorrect_Use_Of_Annotation
                 (Annot_Function_With_Side_Effects, Ent, Name => Prag_Name);
               return;
            elsif Is_Volatile_Function (Ent) then
               Mark_Incorrect_Use_Of_Annotation
                 (Annot_Volatile_Function, Ent, Name => Prag_Name);
               return;
            end if;

            --  Functions which do not mention the container type are treated
            --  specially. They are stored in a map and compatibility checks
            --  on them are deferred.
            --  Keys to store delayed functions annotated with container
            --  aggregates are the enclosing list of declarations and the
            --  base type of the element or key type. They will be used to
            --  find the corresponding function from a container type (in the
            --  same list of declarations and with compatible components).
            --  Ignore the function if it not in SPARK. We cannot complain as
            --  we do not know what is the container type and whether it is in
            --  SPARK or not. If the container type ends up being in SPARK, we
            --  will complain since the function will be missing.

            if Kind_Str = "default_item" then

               if not In_SPARK (Ent) then
                  return;

               elsif Present (First_Formal (Ent)) then
                  Mark_Incorrect_Use_Of_Annotation
                    (Annot_Subp_Parameter_Number,
                     Ent,
                     Name     => Prag_Name,
                     Cont_Msg => Create ("expected no parameters"));
                  return;
               end if;

               declare
                  Inserted : Boolean;
                  Position : Delayed_Aggregate_Function_Maps.Cursor;
                  use Delayed_Aggregate_Function_Maps;
               begin
                  Delayed_Default_Item.Insert
                    ((Enclosing_List      => List_Containing (Prag),
                      Base_Component_Type => Base_Type (Etype (Ent))),
                     Ent,
                     Position,
                     Inserted);

                  if not Inserted then
                     Mark_Incorrect_Use_Of_Annotation
                       (Annot_Duplicated_Annotated_Entity,
                        Ent,
                        Name     => Prag_Name,
                        Snd_Name => Snd_Name,
                        Cont_Msg =>
                          Create
                            ("& # also returns element type &",
                             Names         =>
                               [Element (Position), Etype (Ent)],
                             Secondary_Loc => Sloc (Element (Position))));
                  end if;
               end;

            elsif Kind_Str = "first" then

               if not In_SPARK (Ent) then
                  return;

               elsif Present (First_Formal (Ent)) then
                  Mark_Incorrect_Use_Of_Annotation
                    (Annot_Subp_Parameter_Number,
                     Ent,
                     Name     => Prag_Name,
                     Cont_Msg => Create ("expected no parameters"));
                  return;

               elsif not Is_Signed_Or_Big_Integer_Type (Etype (Ent)) then
                  Mark_Incorrect_Use_Of_Annotation
                    (Annot_Function_Return_Type,
                     Ent,
                     Name     => Prag_Name,
                     Cont_Msg =>
                       Create
                         ("expected a signed integer type or a subtype of "
                          & "Big_Integer"));
                  return;
               end if;

               declare
                  Inserted : Boolean;
                  Position : Delayed_Aggregate_Function_Maps.Cursor;
                  use Delayed_Aggregate_Function_Maps;
               begin
                  Delayed_First.Insert
                    ((Enclosing_List      => List_Containing (Prag),
                      Base_Component_Type => Base_Type (Etype (Ent))),
                     Ent,
                     Position,
                     Inserted);

                  if not Inserted then
                     Mark_Incorrect_Use_Of_Annotation
                       (Annot_Duplicated_Annotated_Entity,
                        Ent,
                        Name     => Prag_Name,
                        Snd_Name => Snd_Name,
                        Cont_Msg =>
                          Create
                            ("& # returns the same position type &",
                             Names         =>
                               [Element (Position), Etype (Ent)],
                             Secondary_Loc => Sloc (Element (Position))));
                  end if;
               end;

            elsif Kind_Str in "equivalent_elements" | "equivalent_keys" then

               if not In_SPARK (Ent) then
                  return;

               elsif Number_Formals (Ent) /= 2 then
                  Mark_Incorrect_Use_Of_Annotation
                    (Annot_Subp_Parameter_Number,
                     Ent,
                     Name     => Prag_Name,
                     Cont_Msg => Create ("expected 2 parameters"));
                  return;

               elsif not Is_Standard_Boolean_Type (Etype (Ent)) then
                  Mark_Incorrect_Use_Of_Annotation
                    (Annot_Function_Return_Type,
                     Ent,
                     Name     => Prag_Name,
                     Cont_Msg => Create ("expected a boolean"));
                  return;

               elsif Etype (First_Formal (Ent))
                 /= Etype (Next_Formal (First_Formal (Ent)))
               then
                  Mark_Incorrect_Use_Of_Annotation
                    (Annot_Subp_Parameter_Type,
                     Ent,
                     Cont_Msg =>
                       Create
                         ("parameters of equivalence relations shall "
                          & "have the same type"));
                  return;
               end if;

               if Kind_Str = "equivalent_elements" then
                  declare
                     Inserted : Boolean;
                     Position : Delayed_Aggregate_Function_Maps.Cursor;
                     use Delayed_Aggregate_Function_Maps;
                  begin
                     Delayed_Equivalent_Elements.Insert
                       ((Enclosing_List      => List_Containing (Prag),
                         Base_Component_Type =>
                           Base_Type (Etype (First_Formal (Ent)))),
                        Ent,
                        Position,
                        Inserted);

                     if not Inserted then
                        Mark_Incorrect_Use_Of_Annotation
                          (Annot_Duplicated_Annotated_Entity,
                           Ent,
                           Name     => Prag_Name,
                           Snd_Name => Snd_Name,
                           Cont_Msg =>
                             Create
                               ("& # has the same element type &",
                                Names         =>
                                  [Element (Position),
                                   Etype (First_Formal (Ent))],
                                Secondary_Loc => Sloc (Element (Position))));
                     end if;
                  end;
               else
                  declare
                     Inserted : Boolean;
                     Position : Delayed_Aggregate_Function_Maps.Cursor;
                     use Delayed_Aggregate_Function_Maps;
                  begin
                     Delayed_Equivalent_Keys.Insert
                       ((Enclosing_List      => List_Containing (Prag),
                         Base_Component_Type =>
                           Base_Type (Etype (First_Formal (Ent)))),
                        Ent,
                        Position,
                        Inserted);

                     if not Inserted then
                        Mark_Incorrect_Use_Of_Annotation
                          (Annot_Duplicated_Annotated_Entity,
                           Ent,
                           Name     => Prag_Name,
                           Snd_Name => Snd_Name,
                           Cont_Msg =>
                             Create
                               ("& # has the same key type &",
                                Names         =>
                                  [Element (Position),
                                   Etype (First_Formal (Ent))],
                                Secondary_Loc => Sloc (Element (Position))));
                     end if;
                  end;
               end if;

            --  Capacity may or may not take the container as a first parameter
            --  depending on whether the capacity of a container is specific to
            --  a container object. Delay it if it takes no parameters.

            elsif Kind_Str = "capacity" then

               if not Is_Signed_Or_Big_Integer_Type (Etype (Ent)) then
                  Mark_Incorrect_Use_Of_Annotation
                    (Annot_Function_Return_Type,
                     Ent,
                     Name     => Prag_Name,
                     Cont_Msg =>
                       Create
                         ("expected a signed integer type or a subtype of "
                          & "Big_Integer"));
                  return;

               elsif No (First_Formal (Ent)) then

                  if not In_SPARK (Ent) then
                     return;
                  end if;

                  declare
                     Inserted : Boolean;
                     Position : Delayed_Aggregate_Function_Maps.Cursor;
                     use Delayed_Aggregate_Function_Maps;
                  begin
                     Delayed_Capacity.Insert
                       ((Enclosing_List      => List_Containing (Prag),
                         Base_Component_Type => Types.Empty),
                        Ent,
                        Position,
                        Inserted);

                     if not Inserted then
                        Mark_Incorrect_Use_Of_Annotation
                          (Annot_Duplicated_Annotated_Entity,
                           Ent,
                           Name     => Prag_Name,
                           Snd_Name => Snd_Name,
                           Cont_Msg =>
                             Create
                               ("& # is declared in the same scope",
                                Names         => [Element (Position)],
                                Secondary_Loc => Sloc (Element (Position))));
                     end if;
                  end;

               else
                  Cont_Ty := Etype (First_Formal (Ent));

                  if not In_SPARK (Cont_Ty) then
                     return;
                  elsif not In_SPARK (Ent) then
                     Mark_Force_Violation
                       (Ent,
                        Reason =>
                          Create
                            ("functions for type with the "
                             & Annot_To_String (Name => Prag_Name)
                             & " are required to be in SPARK",
                             Names => [Cont_Ty]));
                     return;
                  elsif not Has_Aggregate_Annotation (Cont_Ty) then
                     Mark_Incorrect_Use_Of_Annotation
                       (Annot_Subp_Parameter_Type,
                        Ent,
                        Name     => Prag_Name,
                        Cont_Msg =>
                          Create
                            ("type of parameter & shall have the "
                             & Annot_To_String (Name => Prag_Name),
                             Names => [First_Formal (Ent)]));
                     return;
                  elsif List_Containing (Prag)
                    /= List_Containing (Parent (Cont_Ty))
                  then
                     Mark_Incorrect_Use_Of_Annotation
                       (Annot_Entity_Placement,
                        Ent,
                        Name     => Prag_Name,
                        Cont_Msg =>
                          Create
                            ("& shall be declared in the same list of "
                             & "declarations as the partial view of &",
                             Names => [Ent, Cont_Ty]));
                     return;
                  end if;

                  Cont_Ty := Base_Retysp (Cont_Ty);

                  declare
                     Annot : Aggregate_Annotation renames
                       Aggregate_Annotations (Cont_Ty);
                  begin
                     if No (Annot.Spec_Capacity) then
                        Mark_Incorrect_Use_Of_Annotation
                          (Annot_Subp_Parameter_Number,
                           Ent,
                           Name     => Prag_Name,
                           Cont_Msg => Create ("expected no parameters"));
                        return;

                     elsif Number_Formals (Ent) /= 1 then
                        Mark_Incorrect_Use_Of_Annotation
                          (Annot_Subp_Parameter_Number,
                           Ent,
                           Name     => Prag_Name,
                           Cont_Msg => Create ("expected 1 parameter"));
                        return;

                     elsif Present (Annot.Capacity) then
                        Mark_Incorrect_Use_Of_Annotation
                          (Annot_Duplicated_Annotated_Entity,
                           Ent,
                           Name     => Prag_Name,
                           Snd_Name => Snd_Name,
                           Cont_Msg =>
                             Create
                               ("& # has the same container type &",
                                Names         => [Annot.Capacity, Cont_Ty],
                                Secondary_Loc => Sloc (Annot.Capacity)));
                        return;
                     end if;

                     --  Store the capacity function

                     Annot.Capacity := Ent;
                  end;
               end if;
            else

               --  Common checks for other primitives

               if No (First_Formal (Ent)) then
                  Mark_Incorrect_Use_Of_Annotation
                    (Annot_Subp_Parameter_Number,
                     Ent,
                     Name     => Prag_Name,
                     Cont_Msg => Create ("at least one parameter expected"));
                  return;
               end if;

               Cont_Ty := Etype (First_Formal (Ent));

               if not In_SPARK (Cont_Ty) then
                  return;
               elsif not In_SPARK (Ent) then
                  Mark_Force_Violation
                    (Ent,
                     Reason =>
                       Create
                         ("functions for type & with the "
                          & Annot_To_String (Name => Prag_Name)
                          & " are required to be in SPARK",
                          Names => [Cont_Ty]));
                  return;
               elsif not Has_Aggregate_Annotation (Cont_Ty) then
                  Mark_Incorrect_Use_Of_Annotation
                    (Annot_Subp_Parameter_Type,
                     Ent,
                     Name     => Prag_Name,
                     Cont_Msg =>
                       Create
                         ("type of parameter & shall have the "
                          & Annot_To_String (Name => Prag_Name),
                          Names => [First_Formal (Ent)]));
                  return;
               elsif List_Containing (Prag)
                 /= List_Containing (Parent (Cont_Ty))
               then
                  Mark_Incorrect_Use_Of_Annotation
                    (Annot_Entity_Placement,
                     Ent,
                     Name     => Prag_Name,
                     Cont_Msg =>
                       Create
                         ("& shall be declared in the same list of "
                          & "declarations as the partial view of &",
                          Names => [Ent, Cont_Ty]));
                  return;
               end if;

               Cont_Ty := Base_Retysp (Cont_Ty);

               declare
                  Annot : Aggregate_Annotation renames
                    Aggregate_Annotations (Cont_Ty);
               begin
                  case Annot.Kind is
                     when Sets  =>
                        --  The type of the parameters of Contains
                        --  should match those of the Add_Unnamed primitive.
                        --  Length should return an integer type.

                        if Kind_Str = "contains" then
                           if Number_Formals (Ent) /= 2 then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Subp_Parameter_Number,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg => Create ("expected 2 parameters"));
                              return;

                           elsif Present (Annot.Contains) then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Duplicated_Annotated_Entity,
                                 Ent,
                                 Name     => Prag_Name,
                                 Snd_Name => Snd_Name,
                                 Cont_Msg =>
                                   Create
                                     ("& # has the same container type &",
                                      Names         =>
                                        [Annot.Contains, Cont_Ty],
                                      Secondary_Loc => Sloc (Annot.Contains)));
                              return;

                           elsif not Is_Standard_Boolean_Type (Etype (Ent))
                           then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Function_Return_Type,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg => Create ("expected a boolean"));
                              return;

                           elsif Etype (Next_Formal (First_Formal (Ent)))
                             /= Annot.Element_Type
                           then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Subp_Parameter_Type,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg =>
                                   Create
                                     ("parameter & shall have element type &",
                                      Names =>
                                        [Next_Formal (First_Formal (Ent)),
                                         Annot.Element_Type]));
                              return;
                           end if;

                           --  Store the contains function

                           Annot.Contains := Ent;
                        elsif Kind_Str = "length" then
                           if Number_Formals (Ent) /= 1 then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Subp_Parameter_Number,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg => Create ("expected 1 parameter"));
                              return;

                           elsif Present (Annot.Sets_Length) then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Duplicated_Annotated_Entity,
                                 Ent,
                                 Name     => Prag_Name,
                                 Snd_Name => Snd_Name,
                                 Cont_Msg =>
                                   Create
                                     ("& # has the same container type &",
                                      Names         =>
                                        [Annot.Sets_Length, Cont_Ty],
                                      Secondary_Loc =>
                                        Sloc (Annot.Sets_Length)));
                              return;

                           elsif not Is_Signed_Or_Big_Integer_Type
                                       (Etype (Ent))
                           then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Function_Return_Type,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg =>
                                   Create
                                     ("expected a signed integer type or a "
                                      & "subtype of Big_Integer"));
                              return;
                           end if;

                           --  Store the length function

                           Annot.Sets_Length := Ent;
                        else
                           Mark_Incorrect_Use_Of_Annotation
                             (Annot_Wrong_Third_Parameter,
                              Arg3_Exp,
                              From_Aspect => From_Aspect,
                              Name        => Prag_Name);
                           return;
                        end if;

                     when Maps  =>
                        --  The type of the parameters/return type of Has_Key,
                        --  and Get should match those of the Add_Named
                        --  primitive. Length should return an integer type.

                        if Kind_Str = "has_key" then
                           if Number_Formals (Ent) /= 2 then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Subp_Parameter_Number,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg => Create ("expected 2 parameters"));
                              return;

                           elsif Present (Annot.Has_Key) then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Duplicated_Annotated_Entity,
                                 Ent,
                                 Name     => Prag_Name,
                                 Snd_Name => Snd_Name,
                                 Cont_Msg =>
                                   Create
                                     ("& # has the same container type &",
                                      Names         =>
                                        [Annot.Has_Key, Cont_Ty],
                                      Secondary_Loc => Sloc (Annot.Has_Key)));
                              return;

                           elsif not Is_Standard_Boolean_Type (Etype (Ent))
                           then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Function_Return_Type,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg => Create ("expected a boolean"));
                              return;

                           elsif Etype (Next_Formal (First_Formal (Ent)))
                             /= Annot.Key_Type
                           then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Subp_Parameter_Type,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg =>
                                   Create
                                     ("parameter & shall have key type &",
                                      Names =>
                                        [Next_Formal (First_Formal (Ent)),
                                         Annot.Key_Type]));
                              return;
                           end if;

                           --  Store the has_key function

                           Annot.Has_Key := Ent;

                        elsif Kind_Str = "get" then
                           if Number_Formals (Ent) /= 2 then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Subp_Parameter_Number,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg => Create ("expected 2 parameters"));
                              return;

                           elsif Present (Annot.Maps_Get) then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Duplicated_Annotated_Entity,
                                 Ent,
                                 Name     => Prag_Name,
                                 Snd_Name => Snd_Name,
                                 Cont_Msg =>
                                   Create
                                     ("& # has the same container type &",
                                      Names         =>
                                        [Annot.Maps_Get, Cont_Ty],
                                      Secondary_Loc => Sloc (Annot.Maps_Get)));
                              return;

                           elsif Etype (Ent) /= Annot.Element_Type then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Function_Return_Type,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg =>
                                   Create
                                     ("expected element type &",
                                      Names => [Annot.Element_Type]));
                              return;

                           elsif Etype (Next_Formal (First_Formal (Ent)))
                             /= Annot.Key_Type
                           then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Subp_Parameter_Type,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg =>
                                   Create
                                     ("parameter & shall have key type &",
                                      Names =>
                                        [Next_Formal (First_Formal (Ent)),
                                         Annot.Key_Type]));
                              return;
                           end if;

                           --  Store the get function

                           Annot.Maps_Get := Ent;

                        elsif Kind_Str = "length" then
                           if Number_Formals (Ent) /= 1 then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Subp_Parameter_Number,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg => Create ("expected 1 parameter"));
                              return;

                           elsif Present (Annot.Maps_Length) then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Duplicated_Annotated_Entity,
                                 Ent,
                                 Name     => Prag_Name,
                                 Snd_Name => Snd_Name,
                                 Cont_Msg =>
                                   Create
                                     ("& # has the same container type &",
                                      Names         =>
                                        [Annot.Maps_Length, Cont_Ty],
                                      Secondary_Loc =>
                                        Sloc (Annot.Maps_Length)));
                              return;

                           elsif not Is_Signed_Or_Big_Integer_Type
                                       (Etype (Ent))
                           then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Function_Return_Type,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg =>
                                   Create
                                     ("expected a signed integer type or a "
                                      & "subtype of Big_Integer"));
                              return;
                           end if;

                           --  Store the length function

                           Annot.Maps_Length := Ent;

                        else
                           Mark_Incorrect_Use_Of_Annotation
                             (Annot_Wrong_Third_Parameter,
                              Arg3_Exp,
                              From_Aspect => From_Aspect,
                              Name        => Prag_Name);
                           return;
                        end if;

                     when Seqs  =>

                        --  The index parameter of Get and the return type of
                        --  Last should have the same base type. Store it in
                        --  Annot.Index_Type. It will be reset to the subtype
                        --  returned by Last afterward so it can be used to
                        --  determine a potential last possible index if any.
                        --  The fact that the index type is an integer type is
                        --  checked on the first occurrence.

                        if Kind_Str = "get" then
                           if Number_Formals (Ent) /= 2 then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Subp_Parameter_Number,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg => Create ("expected 2 parameters"));
                              return;

                           elsif Present (Annot.Seqs_Get) then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Duplicated_Annotated_Entity,
                                 Ent,
                                 Name     => Prag_Name,
                                 Snd_Name => Snd_Name,
                                 Cont_Msg =>
                                   Create
                                     ("& # has the same container type &",
                                      Names         =>
                                        [Annot.Seqs_Get, Cont_Ty],
                                      Secondary_Loc => Sloc (Annot.Seqs_Get)));
                              return;

                           elsif Etype (Ent) /= Annot.Element_Type then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Function_Return_Type,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg =>
                                   Create
                                     ("expected element type &",
                                      Names => [Annot.Element_Type]));
                              return;

                           elsif Present (Annot.Index_Type)
                             and then
                               Base_Type
                                 (Etype (Next_Formal (First_Formal (Ent))))
                               /= Annot.Index_Type
                           then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Subp_Parameter_Type,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg =>
                                   Create
                                     ("parameter & shall have index type &",
                                      Names =>
                                        [Next_Formal (First_Formal (Ent)),
                                         Annot.Index_Type]));
                              return;

                           elsif No (Annot.Index_Type)
                             and then
                               not Is_Signed_Or_Big_Integer_Type
                                     (Etype (Next_Formal (First_Formal (Ent))))
                           then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Subp_Parameter_Type,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg =>
                                   Create
                                     ("parameter & shall be a signed integer "
                                      & "type or a subtype of Big_Integer",
                                      Names =>
                                        [Next_Formal (First_Formal (Ent))]));
                              return;
                           end if;

                           --  Store the get function

                           Annot.Seqs_Get := Ent;
                           Annot.Index_Type :=
                             Base_Type
                               (Etype (Next_Formal (First_Formal (Ent))));

                        elsif Kind_Str = "last" then
                           if Number_Formals (Ent) /= 1 then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Subp_Parameter_Number,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg => Create ("expected 1 parameter"));
                              return;

                           elsif Present (Annot.Last) then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Duplicated_Annotated_Entity,
                                 Ent,
                                 Name     => Prag_Name,
                                 Snd_Name => Snd_Name,
                                 Cont_Msg =>
                                   Create
                                     ("& # has the same container type &",
                                      Names         => [Annot.Last, Cont_Ty],
                                      Secondary_Loc => Sloc (Annot.Last)));
                              return;

                           elsif Present (Annot.Index_Type)
                             and then
                               Base_Type (Etype (Ent)) /= Annot.Index_Type
                           then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Function_Return_Type,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg =>
                                   Create
                                     ("expected a subtype of &",
                                      Names => [Annot.Index_Type]));

                           elsif No (Annot.Index_Type)
                             and then
                               not Is_Signed_Or_Big_Integer_Type (Etype (Ent))
                           then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Function_Return_Type,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg =>
                                   Create
                                     ("expected a signed integer type or a "
                                      & "subtype of Big_Integer"));
                              return;
                           end if;

                           --  Store the last function

                           Annot.Last := Ent;
                           if No (Annot.Index_Type) then
                              Annot.Index_Type := Base_Type (Etype (Ent));
                           end if;

                        else
                           Mark_Incorrect_Use_Of_Annotation
                             (Annot_Wrong_Third_Parameter,
                              Arg3_Exp,
                              From_Aspect => From_Aspect,
                              Name        => Prag_Name);
                           return;
                        end if;

                     when Model =>

                        --  The return type of the Model should have compatible
                        --  aggregates.

                        if Kind_Str = "model" then
                           if Number_Formals (Ent) /= 1 then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Subp_Parameter_Number,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg => Create ("expected 1 parameter"));
                              return;

                           elsif not Has_Aggregate_Annotation (Etype (Ent))
                           then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Function_Return_Type,
                                 Ent,
                                 Name     => Prag_Name,
                                 Cont_Msg =>
                                   Create
                                     ("return type of & shall have the "
                                      & Annot_To_String (Name => Prag_Name),
                                      Names => [Ent]));
                              return;

                           elsif Present (Annot.Model) then
                              Mark_Incorrect_Use_Of_Annotation
                                (Annot_Duplicated_Annotated_Entity,
                                 Ent,
                                 Name     => Prag_Name,
                                 Snd_Name => Snd_Name,
                                 Cont_Msg =>
                                   Create
                                     ("& # has the same container type &",
                                      Names         => [Annot.Model, Cont_Ty],
                                      Secondary_Loc => Sloc (Annot.Model)));
                              return;

                           end if;

                           --  Store the model function

                           Annot.Model := Ent;
                           Annot.Model_Type := Etype (Ent);
                        else
                           Mark_Incorrect_Use_Of_Annotation
                             (Annot_Wrong_Third_Parameter,
                              Arg3_Exp,
                              From_Aspect => From_Aspect,
                              Name        => Prag_Name);
                           return;
                        end if;
                  end case;
               end;
            end if;

            --  Perform check on globals after the rest as the subprogram being
            --  rejected in phase 1 can cause flow to induely add __HEAP as
            --  a global to the program.

            declare
               Globals : Global_Flow_Ids;

            begin
               Get_Globals
                 (Subprogram          => Ent,
                  Scope               => (Ent => Ent, Part => Visible_Part),
                  Classwide           => False,
                  Globals             => Globals,
                  Use_Deduced_Globals => not Gnat2Why_Args.Global_Gen_Mode,
                  Ignore_Depends      => False);

               if not Globals.Proof_Ins.Is_Empty
                 or else not Globals.Inputs.Is_Empty
                 or else not Globals.Outputs.Is_Empty
               then
                  Mark_Incorrect_Use_Of_Annotation
                    (Annot_Subp_Access_Global, Ent, Name => Prag_Name);
                  return;
               end if;
            end;
         else
            Mark_Incorrect_Use_Of_Annotation
              (Annot_Bad_Entity,
               Ent,
               Cont_Msg => Create ("expected a type or a function"));
         end if;
      end;
   end Check_Aggregate_Annotation;

   ------------------------------------
   -- Check_Annotate_Entity_Argument --
   ------------------------------------

   procedure Check_Annotate_Entity_Argument
     (Arg                 : Node_Id;
      Prag                : Node_Id;
      Prag_Name           : String;
      Continue            : out Boolean;
      Ignore_SPARK_Status : Boolean := False)
   is
      E : Entity_Id;
   begin
      if Nkind (Arg) not in N_Has_Entity then
         Mark_Incorrect_Use_Of_Annotation
           (Annot_Entity_Expected, Arg, Name => Prag_Name);
         Continue := False;
         return;
      end if;
      E := Entity (Arg);
      case Ekind (E) is
         when E_Package | E_Package_Body                            =>
            Continue := True;

         when Subprogram_Kind | Type_Kind | Entry_Kind | E_Constant =>
            Continue := Ignore_SPARK_Status or else In_SPARK (E);

         when Generic_Unit_Kind                                     =>
            --  For generic units: SPARK does not verify anything,
            --  so we delay most checks on instance copy.
            --  We nevertheless check the placement to make sure the pragma
            --  is duplicated on instances.
            Check_Annotate_Placement (E, Prag, Prag_Name, Continue);
            Continue := False;

         when others                                                =>
            Mark_Incorrect_Use_Of_Annotation
              (Annot_Bad_Entity,
               Arg,
               Name        => Prag_Name,
               From_Aspect => From_Aspect_Specification (Prag),
               Cont_Msg    =>
                 Create
                   ("expected a subprogram, a type, a constant, or a "
                    & "package"));
            Continue := False;
      end case;
   end Check_Annotate_Entity_Argument;

   ------------------------------
   -- Check_Annotate_Placement --
   ------------------------------

   procedure Check_Annotate_Placement
     (Ent           : Entity_Id;
      Ent_Decl_Kind : Annotate_Placement_Kind;
      Prag          : Node_Id;
      Prag_Name     : String;
      Decl_Name     : String;
      Ok            : out Boolean)
   is
      Cursor   : Node_Id := Prag;
      Target   : Node_Id;
      Base_Ent : Entity_Id;
      From_Asp : constant Boolean := From_Aspect_Specification (Prag);
      Aspect   : constant Node_Id :=
        (if From_Asp then Corresponding_Aspect (Prag) else Types.Empty);
   begin
      if From_Asp then
         Ok :=
           Ent_Decl_Kind not in Placed_At_Private_View | Placed_At_Full_View
           or else
             Aspect_On_Partial_View (Aspect)
             = (Ent_Decl_Kind = Placed_At_Private_View);
      elsif not Is_List_Member (Cursor) then
         Ok := False;
      else
         case Ent_Decl_Kind is
            when Placed_At_Specification      =>
               case Ekind (Ent) is
                  when Generic_Subprogram_Kind     =>
                     --  For generic subprograms, only aspect form of
                     --  annotate will be duplicated as instances.
                     Ok := False;
                     Mark_Incorrect_Use_Of_Annotation
                       (Kind        => Annot_Pragma_On_Generic,
                        N           => Prag,
                        From_Aspect => False);
                     return;

                  when E_Generic_Package           =>
                     Target := Empty;

                  when E_Package | Subprogram_Kind =>
                     Base_Ent := Get_Renamed_Entity (Ent);
                     Target := Parent (Declaration_Node (Base_Ent));
                     if Nkind (Atree.Parent (Target)) = N_Compilation_Unit then
                        --  For compilation units, pragmas are located at
                        --  a special place in the tree. Note that the target
                        --  node might be the pragma we are looking
                        --  for already.
                        Target :=
                          First
                            (Pragmas_After
                               (Aux_Decls_Node (Atree.Parent (Target))));
                     elsif Ekind (Ent) in Subprogram_Kind
                       and then Is_Generic_Instance (Base_Ent)
                     then
                        --  For generic instances of subprograms,
                        --  the non-aspect pragmas are necessarily placed
                        --  after the instantiation node.
                        Target :=
                          Sem_Ch12.Get_Unit_Instantiation_Node
                            (Defining_Entity (Parent (Target)));
                     end if;

                  when Entry_Kind                  =>
                     Target := Declaration_Node (Ent);

                  when others                      =>
                     raise Program_Error;
               end case;

            when Placed_At_Declaration
               | Placed_At_Full_View
               | Placed_At_Private_View
               | Placed_At_Task_Specification =>
               pragma Assert (Ekind (Ent) in Type_Kind | E_Constant);
               Target := Unique_Entity (Ent);
         end case;
         loop
            if No (Cursor) then
               Ok :=
                 Ent_Decl_Kind = Placed_At_Specification
                 and then Ekind (Ent) in E_Package
                 and then
                   Parent (Prag)
                   = Package_Specification (Get_Renamed_Entity (Ent));
               goto Not_Found;
            end if;
            case Ent_Decl_Kind is
               when Placed_At_Specification      =>
                  exit when Cursor = Target;

               when Placed_At_Task_Specification =>
                  exit when
                    Nkind (Cursor) in N_Task_Type_Declaration
                    and then Unique_Defining_Entity (Cursor) = Target;

               when Placed_At_Full_View          =>
                  exit when
                    Nkind (Cursor) in N_Full_Type_Declaration
                    and then Unique_Defining_Entity (Cursor) = Target;

               when Placed_At_Private_View       =>
                  exit when
                    Nkind (Cursor)
                    in N_Private_Type_Declaration
                     | N_Private_Extension_Declaration
                    and then Unique_Defining_Entity (Cursor) = Target;

               when Placed_At_Declaration        =>
                  exit when
                    Nkind (Cursor) = N_Object_Declaration
                    and then Unique_Defining_Entity (Cursor) = Target;
            end case;
            if Decl_Starts_Pragma_Annotate_Range (Cursor)
              and then not (Nkind (Cursor) in N_Pragma | N_Null_Statement)
            then
               Ok := False;
               goto Not_Found;
            end if;
            Prev (Cursor);
         end loop;
         Ok := True;
         <<Not_Found>>
      end if;
      if not Ok then
         Mark_Incorrect_Use_Of_Annotation
           (Kind        => Annot_Placement,
            N           => Prag,
            From_Aspect => From_Asp,
            Name        => Prag_Name,
            Cont_Msg    =>
              Create
                (Annot_To_String
                   (Format => Aspect_Or_Pragma (From_Asp), Name => Prag_Name)
                 & " must immediately follow the "
                 & Decl_Name));
      end if;
      return;
   end Check_Annotate_Placement;

   procedure Check_Annotate_Placement
     (E : Entity_Id; Prag : Node_Id; Prag_Name : String; Ok : out Boolean) is
   begin
      case Ekind (E) is
         when Subprogram_Kind | Generic_Subprogram_Kind =>
            Check_Annotate_Placement
              (E,
               Placed_At_Specification,
               Prag,
               Prag_Name,
               "specification of subprogram " & Pretty_Source_Name (E),
               Ok);

         when Entry_Kind                                =>
            Check_Annotate_Placement
              (E,
               Placed_At_Specification,
               Prag,
               Prag_Name,
               "declaration of entry " & Pretty_Source_Name (E),
               Ok);

         when E_Package                                 =>
            Check_Annotate_Placement
              (E,
               Placed_At_Specification,
               Prag,
               Prag_Name,
               "beginning or end of package specification "
               & Pretty_Source_Name (E),
               Ok);

         when E_Generic_Package                         =>
            Check_Annotate_Placement
              (E,
               Placed_At_Specification,
               Prag,
               Prag_Name,
               "beginning of package specification " & Pretty_Source_Name (E),
               Ok);

         when E_Task_Type                               =>
            Check_Annotate_Placement
              (E,
               Placed_At_Task_Specification,
               Prag,
               Prag_Name,
               "declaration of task " & Pretty_Source_Name (E),
               Ok);

         when E_Constant                                =>
            Check_Annotate_Placement
              (E,
               Placed_At_Declaration,
               Prag,
               Prag_Name,
               "declaration of constant " & Pretty_Source_Name (E),
               Ok);

         when others                                    =>
            pragma Assert (False);
      end case;
   end Check_Annotate_Placement;

   ------------------------------------
   -- Check_At_End_Borrow_Annotation --
   ------------------------------------

   procedure Check_At_End_Borrow_Annotation
     (Arg3_Exp : Node_Id; Prag : Node_Id)
   is

      procedure Check_At_End_Borrow_Entity (E : Entity_Id; Ok : out Boolean);
      --  E should be a ghost identity expression function taking (and
      --  returning) an access-to-constant type.

      --------------------------------
      -- Check_At_End_Borrow_Entity --
      --------------------------------

      procedure Check_At_End_Borrow_Entity (E : Entity_Id; Ok : out Boolean) is
         Path      : constant Entity_Id := First_Formal (E);
         Contracts : constant Node_Id := Contract (E);
      begin
         Ok := False;
         if No (Path) or else Present (Next_Formal (Path)) then
            Error_Msg_N_If
              ("At_End_Borrow function must have exactly one parameter", E);
         elsif not Is_Ghost_Entity (E) then
            Error_Msg_N_If
              ("At_End_Borrow function must be a ghost function", E);
         elsif Present (Contracts)
           and then
             (Present (Pre_Post_Conditions (Contracts))
              or else Present (Contract_Test_Cases (Contracts)))
         then
            Error_Msg_N_If
              ("At_End_Borrow function should not have a contract", E);

         --  Allow E to not have a body, or to have a body that is not in SPARK

         elsif not Entity_Body_In_SPARK (E) then
            return;

         elsif not Is_Expression_Function_Or_Completion (E) then
            Error_Msg_N_If
              ("At_End_Borrow function must be an expression function", E);

         elsif Potentially_Hidden_Entities.Contains (E) then
            Error_Msg_N_If
              ("a function annotated with Annotate Hide_Info or "
               & "Unhide_Info shall not be annotated with At_End_Borow",
               E);
            return;
         else
            declare
               Expr : constant Node_Id :=
                 Expression (Get_Expression_Function (E));
            begin
               if Nkind (Original_Node (Expr))
                  not in N_Expanded_Name | N_Identifier
                 or else Entity (Original_Node (Expr)) /= Path
               then
                  Error_Msg_N_If
                    ("At_End_Borrow function must be the identity function",
                     E);
               else
                  Ok := True;
               end if;
            end;
         end if;
      end Check_At_End_Borrow_Entity;

      E  : Entity_Id;
      Ok : Boolean;

      --  Start of processing for Check_At_End_Borrow_Annotation

   begin
      Check_Annotate_Entity_Argument (Arg3_Exp, Prag, "At_End_Borrow", Ok);
      if not Ok then
         return;
      end if;
      E := Entity (Arg3_Exp);

      --  This entity must be a function

      if Ekind (E) /= E_Function then
         Error_Msg_N_If
           ("entity parameter of a pragma At_End_Borrow must be a function",
            Arg3_Exp);
         return;
      else
         Check_At_End_Borrow_Entity (E, Ok);
         if not Ok then
            return;
         end if;
         Check_Annotate_Placement (E, Prag, "At_End_Borrow", Ok);
         if not Ok then
            return;
         end if;
      end if;

      --  Go through renamings to find the appropriate entity

      At_End_Borrow_Annotations.Include (Get_Renamed_Entity (E));
   end Check_At_End_Borrow_Annotation;

   --------------------------------------------------------------
   -- Check_Automatic_Inst_And_HO_Specialization_Compatibility --
   --------------------------------------------------------------

   procedure Check_Automatic_Inst_And_HO_Specialization_Compatibility
     (Lemma : Subprogram_Kind_Id; Fun : Function_Kind_Id) is
   begin
      --  Lemma shall to be annotated with higher order specialization

      if not Has_Higher_Order_Specialization_Annotation (Lemma) then
         Warning_Msg_N_If
           (Warn_Auto_Lemma_Higher_Order,
            Lemma,
            Continuations =>
              [Create
                 ("it will not be automatically instantiated on"
                  & " specializations of &",
                  Names => [Fun])]);
         return;
      end if;

      --  Go over the contracts of Lemma to make sure that:
      --   * they contain at least one specializable call to Fun,
      --   * they do not contain partially specializable calls to Fun, and
      --   * all specializable calls to Fun in the contracts of Lemma have
      --     the same specialization.

      declare
         Lemma_Params : Node_Maps.Map;
         --  Map used to simulate a specialized call to Lemma. It will map
         --  its specializable formals to themselves.

         Nb_Fun_Params : Integer := 0;
         --  Number of the specializable parameters of Fun

         Spec_Params : Node_Maps.Map;
         Violation   : Boolean := False;

         function Check_Calls_To_Fun (N : Node_Id) return Traverse_Result;
         --  Return Abandon if N is a non conforming call to Fun. A warning
         --  will have been emitted in this case and Violation will be set to
         --  True. Otherwise, if N is a call to Fun, the Spec_Params map will
         --  be filled with the mapping for the parameters of Fun and OK is
         --  returned.

         function Check_Calls_To_Fun (N : Node_Id) return Traverse_Result is
            Call_Params : Node_Maps.Map;
         begin
            if Nkind (N) = N_Function_Call and then Get_Called_Entity (N) = Fun
            then
               Call_Params := Get_Specialized_Parameters (N, Lemma_Params);

               declare
                  use type Node_Maps.Map;
                  Statically_Specialized_Call : constant Boolean :=
                    (for all E of Call_Params =>
                       not Lemma_Params.Contains (E));
                  --  No specialized parameter of N depends of the parameters
                  --  of Lemma.
                  Totally_Specialized_Call    : constant Boolean :=
                    not Statically_Specialized_Call
                    and then Integer (Call_Params.Length) = Nb_Fun_Params
                    and then
                      (for all E of Call_Params => Lemma_Params.Contains (E));
                  --  All specializable parameters of Fun are associated to
                  --  parameters of Lemma.

               begin
                  --  If N does not take as parameters any of Lemma's
                  --  specializable parameters, then it is irrelevant for the
                  --  specialization of Lemma.

                  if Statically_Specialized_Call then
                     return OK;

                  --  If N takes both parameters of Lemma and other parameters,
                  --  it will be hard to generate the specialized lemma
                  --  instance. We reject it here.

                  elsif not Totally_Specialized_Call then
                     Warning_Msg_N_If
                       (Warn_Auto_Lemma_Calls,
                        Lemma,
                        Names         => [Fun],
                        Continuations =>
                          [Create
                             ("it will not be automatically instantiated on"
                              & " specializations of &",
                              Names => [Fun])]);
                     Violation := True;
                     return Abandon;

                  --  N is the first relevant call to Fun found so far. Store
                  --  the association into Spec_Params.

                  elsif Spec_Params.Is_Empty then
                     Spec_Params := Call_Params;
                     return OK;

                  --  N is consistant with the calls seen so far, continue the
                  --  search.

                  elsif Spec_Params = Call_Params then
                     return OK;

                  --  N is not consistant with the calls seen so far. The
                  --  specialization is ambiguous. We reject it here.

                  else
                     Warning_Msg_N_If
                       (Warn_Auto_Lemma_Different,
                        Lemma,
                        Names         => [Fun],
                        Continuations =>
                          [Create
                             ("it will not be automatically instantiated on"
                              & " specializations of &",
                              Names => [Fun])]);
                     Violation := True;
                     return Abandon;
                  end if;
               end;
            else
               return OK;
            end if;
         end Check_Calls_To_Fun;

         procedure Check_Contract_Of_Lemma is new
           Traverse_More_Proc (Check_Calls_To_Fun);

      begin
         --  Fill the Lemma_Params map and compute Nb_Fun_Params

         declare
            Lemma_Formal : Entity_Id := First_Formal (Lemma);
         begin
            loop
               if Is_Specializable_Formal (Lemma_Formal) then
                  Lemma_Params.Insert (Lemma_Formal, Lemma_Formal);
               end if;
               Next_Formal (Lemma_Formal);
               exit when No (Lemma_Formal);
            end loop;
         end;

         declare
            Fun_Formal : Entity_Id := First_Formal (Fun);
         begin
            loop
               if Is_Specializable_Formal (Fun_Formal) then
                  Nb_Fun_Params := Nb_Fun_Params + 1;
               end if;
               Next_Formal (Fun_Formal);
               exit when No (Fun_Formal);
            end loop;
         end;

         --  Go over the contracts of Lemma and check its calls to Fun. No
         --  need to check the variants here, there is no variant check on
         --  automatic instantiation.

         declare
            Pre  : constant Node_Lists.List :=
              Find_Contracts (Lemma, Pragma_Precondition);
            Post : constant Node_Lists.List :=
              Find_Contracts (Lemma, Pragma_Postcondition);
            CC   : constant Node_Lists.List :=
              Find_Contracts (Lemma, Pragma_Contract_Cases);
         begin
            for N of Pre loop
               Check_Contract_Of_Lemma (N);
               if Violation then
                  goto Violation_Found;
               end if;
            end loop;
            for N of Post loop
               Check_Contract_Of_Lemma (N);
               if Violation then
                  goto Violation_Found;
               end if;
            end loop;
            for N of CC loop
               Check_Contract_Of_Lemma (N);
               if Violation then
                  goto Violation_Found;
               end if;
            end loop;
         end;

         <<Violation_Found>>

         --  If Violation is True, a warning has been emitted already. Exit
         --  the function.

         if Violation then
            return;

         --  Check that the lemma contains at least a call to Fun

         elsif Spec_Params.Is_Empty then
            Warning_Msg_N_If
              (Warn_Auto_Lemma_Specializable,
               Lemma,
               Names         => [Fun],
               Continuations =>
                 [Create
                    ("it will not be automatically instantiated on"
                     & " specializations of &",
                     Names => [Fun])]);
            return;
         end if;

         --  Insert Lemma in the set of lemmas to be considered for
         --  specializations of Fun and store its associated parameter mapping
         --  in Higher_Order_Lemma_Specializations.

         Higher_Order_Spec_Annotations (Fun).Insert (Lemma);
         Higher_Order_Lemma_Specializations.Insert (Lemma, Spec_Params);
      end;
   end Check_Automatic_Inst_And_HO_Specialization_Compatibility;

   ----------------------------------------------
   -- Check_Automatic_Instantiation_Annotation --
   ----------------------------------------------

   procedure Check_Automatic_Instantiation_Annotation
     (Arg3_Exp : Node_Id; Prag : Node_Id)
   is
      From_Aspect      : constant Boolean := From_Aspect_Specification (Prag);
      Aspect_Or_Pragma : constant String :=
        (if From_Aspect then "aspect" else "pragma");
      E                : Entity_Id;
      Ok               : Boolean;
   begin
      --  The third argument must be an entity

      Check_Annotate_Entity_Argument
        (Arg3_Exp, Prag, "Automatic_Instantiation", Ok);
      if not Ok then
         return;
      end if;

      E := Entity (Arg3_Exp);
      pragma Assert (Present (E));

      --  This entity must be a ghost procedure

      if Ekind (E) /= E_Procedure then
         Error_Msg_N_If
           ("entity annotated with the "
            & Aspect_Or_Pragma
            & " Automatic_Instantiation must be a procedure",
            Arg3_Exp);
         return;
      elsif not Is_Ghost_Entity (E) then
         Error_Msg_N_If
           ("procedure annotated with the "
            & Aspect_Or_Pragma
            & " Automatic_Instantiation must be ghost",
            E);
         return;
      elsif No_Return (E) then
         Error_Msg_N_If
           ("No_Return procedure cannot be annotated with the "
            & Aspect_Or_Pragma
            & " Automatic_Instantiation",
            E);
         return;
      elsif Has_Exceptional_Contract (E) then
         Error_Msg_N_If
           ("procedure annotated with the "
            & Aspect_Or_Pragma
            & " Automatic_Instantiation shall not propagate exceptions",
            E);
         return;
      elsif Has_Program_Exit (E) then
         Error_Msg_N_If
           ("procedure annotated with the "
            & Aspect_Or_Pragma
            & " Automatic_Instantiation shall not exit the program",
            E);
         return;
      elsif Mutable_In_Params_Annotations.Contains (E) then
         Error_Msg_N_If
           ("procedure annotated with the "
            & Aspect_Or_Pragma
            & " Automatic_Instantiation shall not have"
            & " mutable ""in"" parameters",
            E);
         return;
      end if;

      --  It shall not have mutable parameters

      declare
         Formal : Entity_Id := First_Formal (E);
      begin
         while Present (Formal) loop
            if Ekind (Formal) /= E_In_Parameter
              or else
                (Is_Access_Object_Type (Etype (Formal))
                 and then not Is_Access_Constant (Etype (Formal)))
            then
               declare
                  Param_String : constant String :=
                    (case Ekind (Formal) is
                       when E_In_Out_Parameter => """in out"" parameters",
                       when E_Out_Parameter    => """out"" parameters",
                       when E_In_Parameter     =>
                         "parameters of an access-to-variable type",
                       when others             => raise Program_Error);
               begin
                  Error_Msg_N_If
                    ("procedure annotated with the "
                     & Aspect_Or_Pragma
                     & " Automatic_Instantiation shall not have "
                     & Param_String,
                     Formal);
                  return;
               end;
            end if;
            Next_Formal (Formal);
         end loop;
      end;

      --  The procedure shall not update any global data

      declare
         Globals : Global_Flow_Ids;
      begin
         Get_Globals
           (Subprogram          => E,
            Scope               => (Ent => E, Part => Visible_Part),
            Classwide           => False,
            Globals             => Globals,
            Use_Deduced_Globals => not Gnat2Why_Args.Global_Gen_Mode,
            Ignore_Depends      => False);

         if not Globals.Outputs.Is_Empty then
            Error_Msg_N_If
              ("procedure annotated with the "
               & Aspect_Or_Pragma
               & " Automatic_Instantiation shall not have global"
               & " outputs",
               E);
            return;
         end if;
      end;

      Check_Annotate_Placement (E, Prag, "Automatic_Instantiation", Ok);
      if not Ok then
         return;
      end if;

      --  Check that E is declared directly after a function

      declare
         Decl      : constant Node_Id := Parent (Declaration_Node (E));
         AI_Pragma : Node_Id := Empty;
         Cur       : Node_Id := Decl;

      begin
         loop
            Prev (Cur);

            --  No functions were found before E

            if No (Cur) then
               Error_Msg_N_If
                 ("procedure annotated with the "
                  & Aspect_Or_Pragma
                  & " Automatic_Instantiation shall be declared directly"
                  & " after a function",
                  E);
               return;

            --  Remember the last pragma Automatic_Instantiation seen so we
            --  can check whether a ghost procedure is an automatically
            --  instantiated lemma if we encounter one.

            elsif Is_Pragma_Annotate_GNATprove (Cur)
              and then Is_Pragma_Annotate_Automatic_Instantiation (Cur)
            then
               AI_Pragma := Cur;

            --  Ignore other pragmas and compiler introduced declarations

            elsif Nkind (Cur) = N_Pragma
              or else not Decl_Starts_Pragma_Annotate_Range (Cur)
            then
               null;

            --  Check that Cur is a function declaration. If so, add the
            --  association to the Automatic_Instantiation_Annotations map.
            --  We assume that lemma procedures associated to a function are
            --  declared just after the function, possibly interspaced with
            --  compiler generated stuff and pragmas and that the pragma
            --  Automatic_Instantiation is always located directly after the
            --  lemma procedure declaration.

            elsif Nkind (Cur) = N_Subprogram_Declaration then
               declare
                  Prec : constant Entity_Id := Unique_Defining_Entity (Cur);

               begin
                  --  Lemmas cannot be associated to functions with
                  --  side effects.

                  if Ekind (Prec) = E_Function
                    and then Is_Function_With_Side_Effects (Prec)
                  then
                     Error_Msg_N_If
                       ("procedure annotated with the "
                        & Aspect_Or_Pragma
                        & " Automatic_Instantiation shall not be declared"
                        & " after a function with side effects",
                        E);
                     return;

                  --  Lemmas cannot be associated to volatile functions

                  elsif Ekind (Prec) = E_Function
                    and then Is_Volatile_Function (Prec)
                  then
                     Error_Msg_N_If
                       ("procedure annotated with the "
                        & Aspect_Or_Pragma
                        & " Automatic_Instantiation shall not be declared"
                        & " after a volatile function",
                        E);
                     return;

                  --  A function has been found, add the association to the
                  --  Automatic_Instantiation_Annotations map and exit the
                  --  loop.

                  elsif Ekind (Prec) = E_Function then
                     Automatic_Instantiation_Annotations.Insert (E, Prec);

                     --  If Prec has higher order specialization, then checks
                     --  need to be done to ensure that E can be specialized.
                     --  This checks is delayed as we do not know in which
                     --  order the higher order specialization and
                     --  automatic instantiation annotations will be analyzed.

                     Delayed_Checks_For_Lemmas.Insert (E);
                     exit;

                  --  Ignore ghost procedures annotated with automatic
                  --  instantiation.

                  elsif Is_Ghost_Entity (Prec)
                    and then Present (AI_Pragma)
                    and then
                      Is_Pragma_Annotate_Automatic_Instantiation
                        (AI_Pragma, Prec)
                  then
                     pragma Assert (Ekind (Prec) = E_Procedure);
                     AI_Pragma := Empty;

                  --  Lemmas cannot be associated to procedures

                  else
                     Error_Msg_N_If
                       ("procedure annotated with the "
                        & Aspect_Or_Pragma
                        & " Automatic_Instantiation shall not be declared"
                        & " after a procedure",
                        E);
                     return;
                  end if;
               end;

            --  The declaration before E is not a function declaration

            else
               Error_Msg_N_If
                 ("procedure annotated with the "
                  & Aspect_Or_Pragma
                  & " Automatic_Instantiation shall be declared directly"
                  & " after a function",
                  E);
               return;
            end if;
         end loop;
      end;
   end Check_Automatic_Instantiation_Annotation;

   ------------------------------
   -- Check_Handler_Annotation --
   ------------------------------

   procedure Check_Handler_Annotation (Arg3_Exp : Node_Id; Prag : Node_Id) is
      From_Aspect      : constant Boolean := From_Aspect_Specification (Prag);
      Aspect_Or_Pragma : constant String :=
        (if From_Aspect then "aspect" else "pragma");
      E                : Entity_Id;
      Ok               : Boolean;
      Pre, Post        : Node_Lists.List;
   begin
      Check_Annotate_Entity_Argument (Arg3_Exp, Prag, "Handler", Ok);
      if not Ok then
         return;
      end if;

      E := Entity (Arg3_Exp);

      Check_Annotate_Placement
        (E,
         Placed_At_Full_View,
         Prag,
         "Handler",
         "full type declaration of " & Pretty_Source_Name (E),
         Ok);
      if not Ok then
         return;
      end if;

      if not Is_Access_Subprogram_Type (E) then
         Error_Msg_N_If
           ("entity annotated with the "
            & Aspect_Or_Pragma
            & " Handler must be an access-to-subprogram type",
            Arg3_Exp);
         return;
      elsif not Is_Library_Level_Entity (E) then
         Error_Msg_N_If
           ("access-to-subprogram type annotated with the "
            & Aspect_Or_Pragma
            & " Handler shall be declared at library level",
            Arg3_Exp);
         return;
      end if;

      Pre :=
        Find_Contracts (Directly_Designated_Type (E), Pragma_Precondition);
      Post :=
        Find_Contracts (Directly_Designated_Type (E), Pragma_Postcondition);

      if not Pre.Is_Empty then
         Error_Msg_N_If
           ("access-to-subprogram type annotated with the "
            & Aspect_Or_Pragma
            & " Handler shall not have a precondition",
            Pre.First_Element);
         return;

      elsif not Post.Is_Empty then
         Error_Msg_N_If
           ("access-to-subprogram type annotated with the "
            & Aspect_Or_Pragma
            & " Handler shall not have a postcondition",
            Post.First_Element);
         return;
      end if;

      pragma
        Assert
          (not Has_Contracts
                 (Directly_Designated_Type (E), Pragma_Contract_Cases));

      Handler_Annotations.Insert (Base_Retysp (E));
   end Check_Handler_Annotation;

   ---------------------------
   -- Check_Hide_Annotation --
   ---------------------------

   procedure Check_Hide_Annotation
     (Aspect_Or_Pragma : String;
      Arg3_Exp         : Node_Id;
      Arg4_Exp         : Node_Id;
      Unhide           : Boolean;
      Prag             : Node_Id)
   is
      use type Opt.SPARK_Mode_Type;
      From_Aspect : constant Boolean := From_Aspect_Specification (Prag);
      Annot       : constant String :=
        (if Unhide then "Unhide_Info" else "Hide_Info");
      Ok          : Boolean;
      Ent         : Entity_Id;
      Default     : Boolean;
      Scope       : Entity_Id;
   begin
      --  If provided, the 4th argument must be an entity

      if Present (Arg4_Exp) then
         Check_Annotate_Entity_Argument
           (Arg4_Exp, Prag, Annot, Ok, Ignore_SPARK_Status => True);
         if not Ok then
            return;
         end if;
         Ent := Entity (Arg4_Exp);
      else
         Ent := Empty;
      end if;

      if Nkind (Arg3_Exp) not in N_String_Literal then

         Mark_Incorrect_Use_Of_Annotation
           (Annot_String_Third_Argument,
            Arg3_Exp,
            Name        => Annot,
            From_Aspect => From_Aspect);
         return;
      end if;

      if To_Lower (To_String (Strval (Arg3_Exp))) = "package_body" then

         --  If Prag comes from an aspect, expect a package body

         if From_Aspect_Specification (Prag) then

            if Ekind (Ent) /= E_Package_Body then
               Error_Msg_N_If
                 ("aspect Annotate "
                  & Annot
                  & " for "
                  & "package bodies shall be specified on a package body",
                  Prag);
               return;
            end if;
            Ent := Unique_Entity (Ent);
            Ok := True;

         --  Otherwise, expect only 3 parameterse

         elsif Present (Ent) then
            Mark_Incorrect_Use_Of_Annotation
              (Annot_Argument_Number,
               Prag,
               Name        => Annot,
               Snd_Name    => "Package_Body",
               From_Aspect => From_Aspect,
               Cont_Msg    => Create ("expected 3 arguments"));
            return;

         --  Check that the pragma is located at the beginning of Ent's
         --  body's declarations.

         else
            --  Look for an immediately enclosing package if any.

            declare
               Par : constant Node_Id := Parent (Prag);
            begin
               if No (Par)
                 or else not Is_List_Member (Prag)
                 or else Nkind (Par) /= N_Package_Body
                 or else List_Containing (Prag) /= Declarations (Par)
               then
                  Ok := False;
               else
                  Ent := Unique_Defining_Entity (Par);
                  Ok := True;

                  declare
                     Decl : Node_Id := First (List_Containing (Prag));
                  begin
                     while Decl /= Prag loop
                        if Decl_Starts_Pragma_Annotate_Range (Decl)
                          and then
                            not (Nkind (Decl) in N_Pragma | N_Null_Statement)
                        then
                           Ok := False;
                           exit;
                        end if;
                        Next (Decl);
                     end loop;
                  end;
               end if;
            end;
         end if;

         if not Ok then
            Error_Msg_N_If
              ("pragma Annotate "
               & Annot
               & " shall be located at the top "
               & "of the declarations of a package body",
               Prag);
            return;

         elsif not Unhide then
            Error_Msg_N_If
              ("pragma Annotate "
               & Annot
               & " cannot be "
               & "applied to package bodies",
               Prag);
            return;

         elsif Is_Compilation_Unit (Ent) then
            --  Special case: ignore such annotation pragma on package bodies
            --  of generic units.

            if not Is_Generic_Instance (Get_Renamed_Entity (Ent)) then
               Error_Msg_N_If
                 ("the entity of a pragma Annotate "
                  & Annot
                  & " for "
                  & "package bodies shall not be a compilation unit",
                  Prag);
            end if;
            return;
         end if;

         Potentially_Hidden_Entities.Include (Ent, Unhide_Package_Body);

      elsif To_Lower (To_String (Strval (Arg3_Exp))) = "private_part" then

         --  Ent should not be provided

         if Present (Ent) then
            Error_Msg_N_If
              ("a pragma Annotate "
               & Annot
               & " for "
               & "private part shall have 3 parameters",
               Prag);
            return;
         end if;

         --  Look for an enclosing package private part

         declare
            Par : constant Node_Id := Parent (Prag);
         begin
            if No (Par)
              or else not Is_List_Member (Prag)
              or else Nkind (Par) /= N_Package_Specification
              or else List_Containing (Prag) /= Private_Declarations (Par)
            then
               Ok := False;
            else
               Ent := Unique_Defining_Entity (Parent (Par));

               --  Check that the pragma is located at the beginning of Ent's
               --  private declarations.

               Ok := True;
               declare
                  Decl : Node_Id := First (List_Containing (Prag));
               begin
                  while Decl /= Prag loop
                     if Decl_Starts_Pragma_Annotate_Range (Decl)
                       and then
                         not (Nkind (Decl) in N_Pragma | N_Null_Statement)
                     then
                        Ok := False;
                        exit;
                     end if;
                     Next (Decl);
                  end loop;
               end;
            end if;
         end;

         if not Ok then
            Error_Msg_N_If
              ("pragma Annotate "
               & Annot
               & " shall be located at the"
               & " top of the private declarations of a package",
               Prag);
            return;

         elsif Unhide then
            Error_Msg_N_If
              ("pragma Annotate "
               & Annot
               & " cannot be applied to private "
               & "part",
               Prag);
            return;

         elsif not Is_Globally_Visible (Ent) then
            --  Special case: ignore such annotation pragma on private parts of
            --  generic units.

            if not Is_Generic_Instance (Get_Renamed_Entity (Ent)) then
               Error_Msg_N_If
                 ("pragma Annotate "
                  & Annot
                  & " for "
                  & "private parts shall be in a visible package",
                  Prag);
            end if;
            return;

         elsif No (SPARK_Pragma (Ent))
           or else
             Get_SPARK_Mode_From_Annotation (SPARK_Pragma (Ent)) /= Opt.On
         then
            Error_Msg_N_If
              ("package annotated with a pragma Annotate "
               & Annot
               & " for "
               & "private parts shall be in SPARK",
               Prag);
            return;
         end if;

         Potentially_Hidden_Private_Parts.Include (Ent, True);

      elsif To_Lower (To_String (Strval (Arg3_Exp)))
        = "expression_function_body"
      then

         --  Ent should be provided

         if No (Ent) then
            Error_Msg_N_If
              ("a pragma Annotate "
               & Annot
               & " for "
               & "expression function bodies shall have 4 parameters",
               Prag);
            return;
         end if;

         --  Search the node to which the current annotation applies. For
         --  aspects, it is the 4th parameter. For pragmas, look for a
         --  declaration or body directly before or enclosing Prag. Default is
         --  set to True if Ent itself is annotated with Hide_Info. In this
         --  case, Ent is considered to be hidden by default.

         if From_Aspect_Specification (Prag) then
            Scope := Ent;
            Default := not Unhide;
         else
            Scope := Annot_Applies_To (Prag);
            if No (Scope) then
               Error_Msg_N_If
                 (Aspect_Or_Pragma
                  & " Annotate "
                  & Annot
                  & " must appear at the beginning of a subprogram, entry, or "
                  & "package body, or just after a subprogram, entry, or "
                  & "package body or declaration",
                  Prag);
               return;
            end if;
            Default := not Unhide and then Scope = Ent;
         end if;

         --  If Scope is not in the analyzed files, only process defaults

         if not Default and then not Is_In_Analyzed_Files (Scope) then
            return;

         elsif not Is_Expression_Function_Or_Completion (Ent) then

            --  If Scope is not in the analyzed files, the annotation is a
            --  default. It is possible that we do not have visibility on the
            --  body of Ent. Ignore the annotation in that case, the body is
            --  always hidden.

            if Is_In_Analyzed_Files (Scope) or else Ekind (Ent) /= E_Function
            then
               Error_Msg_N_If
                 ("the entity of a pragma Annotate "
                  & Annot
                  & " for "
                  & "expression function bodies shall be an expression"
                  & " function",
                  Arg4_Exp);
            end if;
            return;

         elsif not In_SPARK (Ent) then
            Error_Msg_N_If
              ("an expression function annotated with Annotate "
               & Annot
               & " shall be in SPARK",
               Arg4_Exp);
            return;

         elsif not Entity_Body_Compatible_With_SPARK (Ent) then
            Error_Msg_N_If
              ("the body of an expression function annotated with Annotate "
               & Annot
               & " shall be compatible with SPARK",
               Arg4_Exp);
            return;

         elsif Has_Contracts (Ent, Pragma_Refined_Post) then
            Error_Msg_N_If
              ("an expression function annotated with Annotate "
               & Annot
               & " shall not have a refined postcondition",
               Arg4_Exp);
            return;

         elsif Inline_Annotations.Contains (Ent) then
            Error_Msg_N_If
              ("an expression function annotated with Annotate "
               & Annot
               & " shall not be inlined for proof",
               Arg4_Exp);
            return;

         elsif Has_At_End_Borrow_Annotation (Ent) then
            Error_Msg_N_If
              ("an expression function annotated with Annotate "
               & Annot
               & " shall not be annotated with At_End_Borow",
               Arg4_Exp);
            return;

         elsif Has_Logical_Eq_Annotation (Ent) then
            Error_Msg_N_If
              ("an expression function annotated with Annotate "
               & Annot
               & " shall not be a logical equality",
               Arg4_Exp);
            return;

         elsif Has_Higher_Order_Specialization_Annotation (Ent) then
            Error_Msg_N_If
              ("an expression function annotated with Annotate "
               & Annot
               & " shall not have higher-order specialization",
               Arg4_Exp);
            return;
         end if;

         --  Insert specific annotations in Hide_Or_Unhide_Annotations

         if not Default then
            declare
               Kind      : constant Hide_Annotation_Kind :=
                 (if Unhide then Unhide_Expr_Fun else Hide_Expr_Fun);
               Inserted  : Boolean;
               Position  : Hide_Annotations_Maps.Cursor;
               Inner_Pos : Node_To_Hide_Annotation_Kind_Maps.Cursor;
            begin
               Hide_Or_Unhide_Annotations.Insert
                 (Scope,
                  Node_To_Hide_Annotation_Kind_Maps.Empty_Map,
                  Position,
                  Inserted);
               Hide_Or_Unhide_Annotations (Position).Insert
                 (Ent, Kind, Inner_Pos, Inserted);

               --  Check that there is a single Hide or Unhide annotation for
               --  Ent in Scope. We allow duplicating the same annotation, as
               --  such a duplicate might be introduced by the frontend.

               if not Inserted
                 and then
                   Hide_Or_Unhide_Annotations (Position) (Inner_Pos) /= Kind
               then
                  Error_Msg_N_If
                    ("there shall be at most one Hide_Info or Unhide_Info"
                     & " annotation for "
                     & Pretty_Source_Name (Ent)
                     & " in "
                     & Pretty_Source_Name (Scope),
                     Prag);
               end if;
            end;

            --  As the default can change, compatibility checks between the
            --  default and other hide or unhide annotations are deferred.

            Delayed_Hide_Compatibility_Checks.Insert (Prag, (Scope, Ent));
         end if;

         --  Also fill the Potentially_Hidden_Entities map. The default might
         --  change from unhidden to hidden but not the other way around.

         declare
            Kind     : constant Hide_Annotation_Kind :=
              (if Default then Hide_Expr_Fun else Unhide_Expr_Fun);
            Inserted : Boolean;
            Position : Node_To_Hide_Annotation_Kind_Maps.Cursor;
         begin
            Potentially_Hidden_Entities.Insert (Ent, Kind, Position, Inserted);
            if not Inserted and then Default then
               Potentially_Hidden_Entities (Position) := Kind;
            end if;
         end;

      else
         Mark_Incorrect_Use_Of_Annotation
           (Annot_Wrong_Third_Parameter,
            Arg3_Exp,
            Name        => Annot,
            From_Aspect => From_Aspect);
         return;
      end if;
   end Check_Hide_Annotation;

   --------------------------------------------------
   -- Check_Higher_Order_Specialization_Annotation --
   --------------------------------------------------

   procedure Check_Higher_Order_Specialization_Annotation
     (Arg3_Exp : Node_Id; Prag : Node_Id)
   is
      From_Aspect      : constant Boolean := From_Aspect_Specification (Prag);
      Aspect_Or_Pragma : constant String :=
        (if From_Aspect then "aspect" else "pragma");
      E                : Entity_Id;
      Okay             : Boolean;
      --  Ok would shadow enumeration value OK here.
   begin
      --  The third argument must be an entity

      Check_Annotate_Entity_Argument
        (Arg3_Exp, Prag, "Higher_Order_Specialization", Okay);
      if not Okay then
         return;
      end if;

      E := Entity (Arg3_Exp);

      --  This entity must be a function

      if Ekind (E) not in E_Procedure | E_Function then
         Error_Msg_N_If
           (Aspect_Or_Pragma
            & " Higher_Order_Specialization must be applied"
            & " to a function or a lemma procedure",
            Arg3_Exp);
         return;

      --  For now reject volatile functions, functions with side effects,
      --  dispatching operations, and borrowing traversal functions.

      elsif Ekind (E) = E_Function and then Is_Function_With_Side_Effects (E)
      then
         Error_Msg_N_If
           ("function annotated with Higher_Order_Specialization shall not be"
            & " a function with side effects",
            Arg3_Exp);
         return;
      elsif Ekind (E) = E_Function and then Is_Volatile_Function (E) then
         Error_Msg_N_If
           ("function annotated with Higher_Order_Specialization shall not be"
            & " a volatile function",
            Arg3_Exp);
         return;
      elsif Einfo.Entities.Is_Dispatching_Operation (E)
        and then Present (SPARK_Util.Subprograms.Find_Dispatching_Type (E))
      then
         Error_Msg_N_If
           ("subprogram annotated with Higher_Order_Specialization shall not"
            & " be a dispatching operation",
            Arg3_Exp);
         return;
      elsif Is_Borrowing_Traversal_Function (E) then
         Error_Msg_N_If
           ("function annotated with Higher_Order_Specialization shall not be"
            & " a borrowing traversal function",
            Arg3_Exp);
         return;
      elsif Potentially_Hidden_Entities.Contains (E) then
         Error_Msg_N_If
           ("a subprogram annotated with Annotate Hide_Info or "
            & "Unhide_Info shall not have higher-order specialization",
            E);
         return;

      --  For procedures, check that we have a lemma

      elsif Ekind (E) = E_Procedure then

         --  It should be ghost

         if not Is_Ghost_Entity (E) then
            Error_Msg_N_If
              ("procedure annotated with the "
               & Aspect_Or_Pragma
               & " Higher_Order_Specialization shall be ghost",
               E);
            return;
         elsif No_Return (E) then
            Error_Msg_N_If
              ("No_Return procedure cannot be annotated with the "
               & Aspect_Or_Pragma
               & " Higher_Order_Specialization",
               E);
            return;
         elsif Has_Exceptional_Contract (E) then
            Error_Msg_N_If
              ("procedure annotated with the "
               & Aspect_Or_Pragma
               & " Higher_Order_Specialization shall not propagate exceptions",
               E);
            return;
         elsif Has_Program_Exit (E) then
            Error_Msg_N_If
              ("procedure annotated with the "
               & Aspect_Or_Pragma
               & " Higher_Order_Specialization shall not exit the program",
               E);
            return;
         elsif Get_Termination_Condition (E)
               not in (Kind => Unspecified) | (Static, True)
         then
            Error_Msg_N_If
              ("procedure annotated with the "
               & Aspect_Or_Pragma
               & " Higher_Order_Specialization shall have an Always_Terminates"
               & " aspect of True",
               E);
            return;
         end if;

         --  It shall not have mutable parameters

         declare
            Formal : Entity_Id := First_Formal (E);
         begin
            while Present (Formal) loop
               if Ekind (Formal) /= E_In_Parameter
                 or else
                   (Is_Access_Object_Type (Etype (Formal))
                    and then not Is_Access_Constant (Etype (Formal)))
               then
                  declare
                     Param_String : constant String :=
                       (case Ekind (Formal) is
                          when E_In_Out_Parameter => """in out"" parameters",
                          when E_Out_Parameter    => """out"" parameters",
                          when E_In_Parameter     =>
                            "parameters of an access-to-variable type",
                          when others             => raise Program_Error);
                  begin
                     Error_Msg_N_If
                       ("procedure annotated with the "
                        & Aspect_Or_Pragma
                        & "Higher_Order_Specialization shall not have "
                        & Param_String,
                        Formal);
                     return;
                  end;
               end if;
               Next_Formal (Formal);
            end loop;
         end;

         --  It shall not update any global data

         declare
            Globals : Global_Flow_Ids;
         begin
            Get_Globals
              (Subprogram          => E,
               Scope               => (Ent => E, Part => Visible_Part),
               Classwide           => False,
               Globals             => Globals,
               Use_Deduced_Globals => not Gnat2Why_Args.Global_Gen_Mode,
               Ignore_Depends      => False);

            if not Globals.Outputs.Is_Empty then
               Error_Msg_N_If
                 ("procedure annotated with the "
                  & Aspect_Or_Pragma
                  & " Higher_Order_Specialization shall not have global"
                  & " outputs",
                  E);
               return;
            end if;
         end;
      end if;

      --  The body of expression functions is ignored for higher order
      --  specialization. If E should be inline, require a postcondition.

      if Present (Retrieve_Inline_Annotation (E))
        and then
          Find_Contracts (E, Pragma_Postcondition, False, False).Is_Empty
      then
         Error_Msg_N_If
           ("function annotated with both Higher_Order_Specialization and"
            & " Inline_For_Proof shall have a postcondition",
            E);
         return;
      end if;

      declare
         F         : Opt_Formal_Kind_Id := First_Formal (E);
         Formals   : Entity_Sets.Set;
         Violation : Node_Id := Empty;

         function Is_Use_Of_Formal (N : Node_Id) return Traverse_Result
         is (if Nkind (N) in N_Expanded_Name | N_Identifier
               and then Formals.Contains (Unique_Entity (Entity (N)))
             then Abandon
             else OK);

         function Contains_Use_Of_Formal is new
           Traverse_More_Func (Is_Use_Of_Formal);

         function Is_Unsupported_Use_Of_Formal
           (N : Node_Id) return Traverse_Result;
         --  Return Abandon on references to objects of Formals if they are not
         --  directly under a dereference or as actual parameters to call to
         --  functions annotated with Higher_Order_Specialization. In this
         --  case, store the offending node in Violation for error reporting.

         ----------------------------------
         -- Is_Unsupported_Use_Of_Formal --
         ----------------------------------

         function Is_Unsupported_Use_Of_Formal
           (N : Node_Id) return Traverse_Result is
         begin
            --  Uses are allowed under dereferences

            if Nkind (N) = N_Explicit_Dereference
              and then Nkind (Prefix (N)) in N_Expanded_Name | N_Identifier
            then
               return Skip;
            elsif Nkind (N) in N_Expanded_Name | N_Identifier
              and then Present (Entity (N))
              and then Formals.Contains (Unique_Entity (Entity (N)))
            then

               --  Check whether N is a call actual

               declare
                  Formal : Entity_Id;
                  Call   : Node_Id;
                  Callee : Entity_Id;
               begin
                  Find_Actual (N, Formal, Call);

                  --  If so, check that Call is a call to a function annotated
                  --  with Higher_Order_Specialization and Formal is an
                  --  anonymous access-to-function type.

                  if No (Call)
                    or else
                      Nkind (Call)
                      not in N_Function_Call | N_Procedure_Call_Statement
                  then

                     --  Here we probably can only have comparison to null

                     Violation := N;
                     return Abandon;
                  else
                     Callee := Get_Called_Entity (Call);

                     if Ekind (Callee) not in E_Function | E_Procedure
                       or else not Is_Anonymous_Access_Type (Etype (Formal))
                     then
                        Violation := N;
                        return Abandon;

                     --  Callee might not have been marked yet. Store Call in
                     --  Delayed_HO_Specialization_Checks, it will be checked
                     --  later. We use Include and not Insert as a call might
                     --  have several specialized parameters.

                     elsif not Has_Higher_Order_Specialization_Annotation
                                 (Callee)
                     then
                        Delayed_HO_Specialization_Checks.Include (Call, N);
                        return OK;
                     else
                        return OK;
                     end if;
                  end if;
               end;

            --  Inside iterated component associations, we cannot support any
            --  references to the formals. This is because expressions in
            --  iterated associations are translated directly inside the
            --  aggregate module, so the aggregate module itself would have to
            --  be specialized.

            elsif Nkind (N) = N_Iterated_Component_Association
              and then Contains_Use_Of_Formal (N) = Abandon
            then
               Violation := N;
               return Abandon;
            else
               return OK;
            end if;
         end Is_Unsupported_Use_Of_Formal;

         procedure Find_Unsupported_Use_Of_Formal is new
           Traverse_More_Proc (Is_Unsupported_Use_Of_Formal);
      begin
         --  Check that E has at least a parameter of an anonymous
         --  access-to-function type. Store such parameters in a set.

         while Present (F) loop
            if Is_Anonymous_Access_Type (Etype (F))
              and then Is_Access_Subprogram_Type (Etype (F))
              and then Is_Function_Type (Directly_Designated_Type (Etype (F)))
            then
               Formals.Include (Unique_Entity (F));
            end if;
            Next_Formal (F);
         end loop;

         if Formals.Is_Empty then
            Error_Msg_N_If
              ("subprogram annotated with Higher_Order_Specialization shall"
               & " have at least a parameter of an anonymous"
               & " access-to-function type",
               Arg3_Exp);
            return;
         end if;

         --  Go over the contracts of E to make sure that the value of its
         --  anonymous access-to-function parameters is not referenced.
         --  We don't check refined postconditions and expression function
         --  bodies which are never specialized.

         declare
            Pre      : constant Node_Lists.List :=
              Find_Contracts (E, Pragma_Precondition);
            Post     : constant Node_Lists.List :=
              Find_Contracts (E, Pragma_Postcondition);
            CC       : constant Node_Lists.List :=
              Find_Contracts (E, Pragma_Contract_Cases);
            Variants : constant Node_Id :=
              Get_Pragma (E, Pragma_Subprogram_Variant);
         begin
            for N of Pre loop
               Find_Unsupported_Use_Of_Formal (N);
               if Present (Violation) then
                  goto Violation_Found;
               end if;
            end loop;
            for N of Post loop
               Find_Unsupported_Use_Of_Formal (N);
               if Present (Violation) then
                  goto Violation_Found;
               end if;
            end loop;
            for N of CC loop
               Find_Unsupported_Use_Of_Formal (N);
               if Present (Violation) then
                  goto Violation_Found;
               end if;
            end loop;
            Find_Unsupported_Use_Of_Formal (Variants);
         end;

         <<Violation_Found>>
         if Present (Violation) then
            if Nkind (Violation) = N_Iterated_Component_Association then
               Error_Msg_N_If
                 ("subprogram annotated with Higher_Order_Specialization"
                  & " shall not reference its access-to-function"
                  & " parameters inside an iterated component association",
                  Violation);
            else
               Error_Msg_N_If
                 ("subprogram annotated with Higher_Order_Specialization"
                  & " shall only reference its access-to-function"
                  & " parameters in dereferences and as actual parameters in"
                  & " calls to functions annotated with"
                  & " Higher_Order_Specialization",
                  Violation);
            end if;
            return;
         end if;
      end;

      Check_Annotate_Placement (E, Prag, "Higher_Order_Specialization", Okay);
      if not Okay then
         return;
      end if;

      Higher_Order_Spec_Annotations.Include (E, Node_Sets.Empty_Set);
   end Check_Higher_Order_Specialization_Annotation;

   -----------------------------
   -- Check_Inline_Annotation --
   -----------------------------

   procedure Check_Inline_Annotation (Arg3_Exp : Node_Id; Prag : Node_Id) is
      E     : Entity_Id;
      Nodes : Common_Containers.Node_Lists.List;
      Value : Node_Id;
      Ok    : Boolean;

      package NL renames Common_Containers.Node_Lists;

      use type Ada.Containers.Count_Type;

   begin
      --  The third argument must be an entity

      Check_Annotate_Entity_Argument (Arg3_Exp, Prag, "Inline_For_Proof", Ok);
      if not Ok then
         return;
      end if;

      E := Entity (Arg3_Exp);

      --  This entity must be a function

      if Ekind (E) /= E_Function then
         Error_Msg_N_If
           ("Entity parameter of a pragma Inline_For_Proof must be a function",
            Arg3_Exp);
         return;
      end if;

      --  Check if E has a postcondition

      Nodes := Find_Contracts (E, Pragma_Postcondition, False, False);

      --  If it does not have one, it must be an expression function

      if Nodes.Is_Empty then
         if not Is_Expression_Function_Or_Completion (E) then
            Error_Msg_N_If
              ("function with Inline_For_Proof and no postconditions must "
               & "be an expression function",
               E);
            return;
         elsif not SPARK_Definition.Entity_Body_Compatible_With_SPARK (E) then
            Mark_Incorrect_Use_Of_Annotation
              (Annot_Inline_For_Proof_Body_Off, E);
            return;
         else
            Value := Expression (Get_Expression_Function (E));
         end if;

      elsif Nodes.Length > 1 then
         Error_Msg_N_If
           ("function with Inline_For_Proof must be an expression function"
            & " or have exactly one postcondition",
            NL.Element (NL.Next (Nodes.First)));
         return;

      --  Otherwise, its postcondition must be of the form F'Result = Expr

      else

         Value := Nodes.First_Element;

         if Nkind (Value) = N_Op_Eq
           and then Is_Attribute_Result (Left_Opnd (Value))
         then
            Value := Right_Opnd (Value);

         --  Or a call to a user defined equality function

         elsif Nkind (Value) = N_Function_Call
           and then
             (Is_User_Defined_Equality (Get_Called_Entity (Value))
              or else Nkind (Original_Node (Value)) = N_Op_Eq)
           and then Is_Attribute_Result (First_Actual (Value))
         then
            Value := Next_Actual (First_Actual (Value));

         else
            Error_Msg_NE_If
              ("function with Inline_For_Proof must"
               & " have a postcondition of the form ""&'Result = Expr""",
               E,
               E);
            return;
         end if;
      end if;

      --  Inline_For_Proof and Logical_Equal are incompatible

      if Has_Logical_Eq_Annotation (E) then
         Error_Msg_N_If
           ("Entity parameter of a pragma Inline_For_Proof shall not have a"
            & " Logical_Equal annotation",
            Arg3_Exp);
         return;
      end if;

      --  For now reject volatile functions, functions with side effects,
      --  dispatching operations, and borrowing traversal functions.

      if Is_Function_With_Side_Effects (E) then
         Error_Msg_N_If
           ("function annotated with Inline_For_Proof shall not be"
            & " a function with side effects",
            Arg3_Exp);
         return;
      elsif Is_Volatile_Function (E) then
         Error_Msg_N_If
           ("function annotated with Inline_For_Proof shall not be"
            & " a volatile function",
            Arg3_Exp);
         return;
      elsif Einfo.Entities.Is_Dispatching_Operation (E)
        and then Present (SPARK_Util.Subprograms.Find_Dispatching_Type (E))
      then
         Error_Msg_N_If
           ("subprogram annotated with Inline_For_Proof shall not"
            & " be a dispatching operation",
            Arg3_Exp);
         return;
      elsif Is_Borrowing_Traversal_Function (E) then
         Error_Msg_N_If
           ("function annotated with Inline_For_Proof shall not be"
            & " a borrowing traversal function",
            Arg3_Exp);
         return;
      elsif Potentially_Hidden_Entities.Contains (E) then
         Error_Msg_N_If
           ("a function annotated with Annotate Hide_Info or "
            & "Unhide_Info shall not be inlined for proof",
            Arg3_Exp);
         return;
      elsif Is_Potentially_Invalid (E) and then Nodes.Length = 1 then
         Error_Msg_N_If
           ("function annotated with Inline_For_Proof with a postcondition "
            & "shall not have a potentially invalid result",
            E);
         return;
      end if;

      --  The body of expression functions is ignored for higher order
      --  specialization. Require a postcondition.

      if Has_Higher_Order_Specialization_Annotation (E) and then Nodes.Is_Empty
      then
         Error_Msg_N_If
           ("function annotated with both Higher_Order_Specialization and"
            & " Inline_For_Proof shall have a postcondition",
            E);
         return;
      end if;

      Check_Annotate_Placement (E, Prag, "Inline_For_Proof", Ok);
      if not Ok then
         return;
      end if;

      Inline_Annotations.Include (E, Value);
      Inline_Pragmas.Include (E, Prag);
   end Check_Inline_Annotation;

   ------------------------
   -- Check_Is_Annotated --
   ------------------------

   procedure Check_Is_Annotated
     (Node  : Node_Id;
      Msg   : String;
      Check : Boolean;
      Info  : out Annotated_Range)
   is
      Node_Slc : constant Source_Ptr := Sloc (Node);
   begin
      Info := Annotated_Range'(Present => False);

      --  This is a simple linear search in a sorted list, the only subtle
      --  thing is that several entries may match, or entries may include
      --  other entries.

      for E : Annotated_Range of Annotations loop

         --  If the current Annotation_Range starts already after the one we
         --  look for, then we can stop.

         if Node_Slc < E.First then
            return;

         --  This is the case where the ranges match, but we have to check
         --  whether the pattern matches, too.

         elsif Node_Slc <= E.Last
           and then
             Erroutc.Matches
               (S => Msg, P => '*' & String_Value (E.Pattern) & '*')
         then
            Info := E;

            --  Deal with useless pragma Annotate; Check = False means a proved
            --  message.

            if not Check then

               --  If this is the first check which corresponds to this pragma,
               --  it possibly only corresponds to proved checks.

               if Pragma_Set.Contains (Info.Prgma) then
                  Proved_Pragma.Include (Info.Prgma);
               end if;

            --  Check = True means a check message

            else

               --  A real check means the pragma is useful

               Proved_Pragma.Exclude (Info.Prgma);
            end if;

            --  In all cases we have now encountered this pragma and can remove
            --  it from pragma set.

            Pragma_Set.Exclude (Info.Prgma);
            return;

         --  There is nothing to do in this case, but there may be other ranges
         --  later which may still be interesting.

         else
            null;
         end if;
      end loop;
   end Check_Is_Annotated;

   -------------------------------
   -- Check_Iterable_Annotation --
   -------------------------------

   procedure Check_Iterable_Annotation
     (Arg3_Exp : Node_Id; Arg4_Exp : Node_Id; Prag : Node_Id)
   is

      procedure Check_Common_Properties
        (Container_Ty   : Type_Kind_Id;
         E              : Entity_Id;
         Ok             : out Boolean;
         Name_For_Error : String);
      --  Checks that are common for Model/Contains function:
      --  No Globals, not volatile, primitive.

      procedure Check_Contains_Entity
        (E : Entity_Id; Ok : out Boolean; Cont_Element : out Entity_Id);
      --  Checks that E is a valid Contains function for a type with an
      --  Iterable aspect. Initializes Cont_Element correctly if succeeding.

      procedure Check_Model_Entity
        (E : Entity_Id; Ok : out Boolean; Cont_Element : out Entity_Id);
      --  Checks that E is a valid Model function for a type with an
      --  Iterable aspect. Initializes Cont_Element correctly if succeeding.

      function Find_Model_Root (Container_Type : Entity_Id) return Entity_Id;
      --  Computes the final container type at the end of the
      --  model chain for the currently known Iterable_For_Proof(...,"Model")
      --  annotations.

      procedure Process_Iterable_Annotation
        (Kind : Iterable_Kind; Entity : Entity_Id);
      --  Insert an iterable annotation into the Iterable_Annotations map and
      --  mark the iterable functions.

      -----------------------------
      -- Check_Common_Properties --
      -----------------------------

      procedure Check_Common_Properties
        (Container_Ty   : Type_Kind_Id;
         E              : Entity_Id;
         Ok             : out Boolean;
         Name_For_Error : String)
      is
         Globals : Global_Flow_Ids;
      begin
         Ok := False;
         if not In_SPARK (E) then
            Mark_Violation (Arg4_Exp, From => E);
            return;
         end if;
         if List_Containing (Prag) /= List_Containing (Parent (Container_Ty))
         then
            Error_Msg_N_If
              (Name_For_Error
               & " function must be primitive for container type",
               E);
            return;
         end if;
         if Is_Function_With_Side_Effects (E) then
            Error_Msg_N_If
              (Name_For_Error & " function must not have side effects", E);
            return;
         end if;
         if Is_Volatile_Function (E) then
            Error_Msg_N_If
              (Name_For_Error & " function must not be volatile", E);
            return;
         end if;
         Get_Globals
           (Subprogram          => E,
            Scope               => (Ent => E, Part => Visible_Part),
            Classwide           => False,
            Globals             => Globals,
            Use_Deduced_Globals => not Gnat2Why_Args.Global_Gen_Mode,
            Ignore_Depends      => False);
         if not Globals.Proof_Ins.Is_Empty
           or else not Globals.Inputs.Is_Empty
           or else not Globals.Outputs.Is_Empty
         then
            Error_Msg_N_If
              (Name_For_Error & " function shall not access global data", E);
            return;
         else
            Ok := True;
         end if;
      end Check_Common_Properties;

      ---------------------------
      -- Check_Contains_Entity --
      ---------------------------

      procedure Check_Contains_Entity
        (E : Entity_Id; Ok : out Boolean; Cont_Element : out Entity_Id)
      is
         C_Param : constant Node_Id := First_Formal (E);
         E_Param : constant Node_Id :=
           (if Present (C_Param) then Next_Formal (C_Param) else Empty);

         Container_Type : Entity_Id;
         --  Type of the first argument of the Contains function
         Element_Type   : Entity_Id;
         --  Type of the second argument of the Contains function

      begin
         Ok := False;
         Cont_Element := Empty;

         if No (E_Param) or else Present (Next_Formal (E_Param)) then
            Error_Msg_N_If
              ("Contains function must have exactly two parameters", E);
            return;
         end if;

         Container_Type := Etype (C_Param);
         Element_Type := Etype (E_Param);

         if not In_SPARK (Container_Type) then
            return;
         --  No needs for checks if container type is not in SPARK,
         --  the annotation can be silently ignored in that case.

         end if;

         if not Is_Standard_Boolean_Type (Etype (E)) then
            Error_Msg_N_If ("Contains function must return Booleans", E);
         else
            Cont_Element :=
              Get_Iterable_Type_Primitive (Container_Type, Name_Element);
            --  Element primitive of Container_Type
            if No (Cont_Element) then
               Error_Msg_N_If
                 ("first parameter of Contains function must allow for of "
                  & "iteration",
                  C_Param);
            elsif not In_SPARK (Cont_Element) then
               Error_Msg_N_If
                 ("first parameter of Contains functions must allow for of "
                  & "iteration in SPARK",
                  C_Param);
            elsif Retysp (Etype (Cont_Element)) /= Retysp (Element_Type) then
               Error_Msg_N_If
                 ("second parameter of Contains must have the type of "
                  & "elements",
                  E_Param);
            else
               Check_Common_Properties (Container_Type, E, Ok, "Contains");
            end if;
         end if;
      end Check_Contains_Entity;

      ------------------------
      -- Check_Model_Entity --
      ------------------------

      procedure Check_Model_Entity
        (E : Entity_Id; Ok : out Boolean; Cont_Element : out Entity_Id)
      is
         Param : constant Node_Id := First_Formal (E);

         Model_Type : constant Entity_Id := Etype (E);
         --  Return type of the model function

         Container_Type : Entity_Id;
         --  Type of first argument of the model function

         Model_Element : Entity_Id;

      begin
         Ok := False;
         Cont_Element := Empty;

         if No (Param) or else Present (Next_Formal (Param)) then
            Error_Msg_N_If
              ("Model function must have exactly one parameter", E);
            return;
         end if;

         Container_Type := Etype (Param);

         if not In_SPARK (Container_Type) then
            return;
         --  No needs for checks if container type is not in SPARK,
         --  the annotation can be silently ignored in that case.

         end if;

         Cont_Element :=
           Get_Iterable_Type_Primitive (Container_Type, Name_Element);
         Model_Element :=
           Get_Iterable_Type_Primitive (Model_Type, Name_Element);

         if No (Cont_Element) then
            Error_Msg_N_If
              ("parameter of Model function must allow for of iteration",
               Param);
         elsif not In_SPARK (Cont_Element) then
            Error_Msg_N_If
              ("parameter of Model function must allow for of iteration "
               & "in SPARK",
               Param);
         elsif No (Model_Element) then
            Error_Msg_N_If
              ("return type of Model function must allow for of "
               & "iteration",
               E);
         elsif not In_SPARK (Model_Element) then
            Error_Msg_N_If
              ("return type of Model function must allow for of "
               & "iteration in SPARK",
               E);
         elsif Retysp (Etype (Cont_Element)) /= Retysp (Etype (Model_Element))
         then
            Error_Msg_N_If
              ("parameter and return type of Model function must "
               & "allow for of iteration with the same element type",
               E);
         elsif Has_Controlling_Result (E) then
            Error_Msg_N_If
              ("Model function must not have a controlling result", E);
         else
            Check_Common_Properties (Container_Type, E, Ok, "Model");
            if Ok
              and then
                Unchecked_Full_Type (Find_Model_Root (Model_Type))
                = Unchecked_Full_Type (Container_Type)
            then
               Ok := False;
               Error_Msg_N_If
                 ("adding this Model function would produce a circular "
                  & "definition for container model",
                  E);
            end if;
         end if;
      end Check_Model_Entity;

      ---------------------
      -- Find_Model_Root --
      ---------------------

      function Find_Model_Root (Container_Type : Entity_Id) return Entity_Id is
         Cursor : Entity_Id := Container_Type;
         Found  : Boolean := True;
         Annot  : Iterable_Annotation;
      begin
         while Found loop
            Retrieve_Iterable_Annotation (Cursor, Found, Annot);
            if Found then
               case Annot.Kind is
                  when Contains =>
                     Found := False;

                  when Model    =>
                     Cursor := Etype (Annot.Entity);
               end case;
            end if;
         end loop;
         return Cursor;
      end Find_Model_Root;

      ---------------------------------
      -- Process_Iterable_Annotation --
      ---------------------------------

      procedure Process_Iterable_Annotation
        (Kind : Iterable_Kind; Entity : Entity_Id)
      is
         Container_Type : constant Entity_Id := Etype (First_Entity (Entity));
         Iterable_Node  : constant Node_Id :=
           Find_Value_Of_Aspect (Container_Type, Aspect_Iterable);
         Position       : Iterable_Maps.Cursor;
         Inserted       : Boolean;
      begin
         pragma Assert (Present (Iterable_Node));

         Iterable_Annotations.Insert
           (Iterable_Node,
            Iterable_Annotation'(Kind, Entity),
            Position,
            Inserted);

         if not Inserted then
            Error_Msg_NE_If
              ("two Iterable_For_Proof annotations for container type &",
               Entity,
               Container_Type);
            return;
         end if;

      end Process_Iterable_Annotation;

      Args_Str     : constant String_Id := Strval (Arg3_Exp);
      Kind         : Iterable_Kind;
      New_Prim     : Entity_Id;
      Ok           : Boolean;
      Cont_Element : Entity_Id;
      --  "Element" primitive for relevant container.
      --  Set at most once.

      --  Start of processing for Check_Iterable_Annotation

   begin
      --  The fourth argument must be an entity

      Check_Annotate_Entity_Argument
        (Arg4_Exp,
         Prag,
         "Iterable_For_Proof",
         Ok,
         Ignore_SPARK_Status => True);
      if not Ok then
         return;
      end if;

      New_Prim := Entity (Arg4_Exp);

      if Ekind (New_Prim) /= E_Function then
         Error_Msg_N_If
           ("the entity of a Gnatprove Annotate Iterable_For_Proof "
            & "pragma must be a function",
            New_Prim);
         return;
      end if;

      if To_Lower (To_String (Args_Str)) = "model" then
         Kind := Model;
         Check_Model_Entity (New_Prim, Ok, Cont_Element);
      elsif To_Lower (To_String (Args_Str)) = "contains" then
         Kind := Contains;
         Check_Contains_Entity (New_Prim, Ok, Cont_Element);
      else
         Error_Msg_N_If
           ("the third argument of a Gnatprove Annotate Iterable_For_Proof "
            & "pragma must be Model or Contains",
            Arg3_Exp);
         return;
      end if;

      if not Ok then
         return;
      end if;

      Check_Annotate_Placement
        (New_Prim,
         Placed_At_Specification,
         Prag,
         "Iterable_For_Proof",
         "specification of function " & Pretty_Source_Name (New_Prim),
         Ok);
      if not Ok then
         return;
      end if;

      Process_Iterable_Annotation (Kind, New_Prim);

   end Check_Iterable_Annotation;

   ------------------------------------
   -- Check_Logical_Equal_Annotation --
   ------------------------------------

   procedure Check_Logical_Equal_Annotation
     (Arg3_Exp : Node_Id; Prag : Node_Id)
   is
      E  : Entity_Id;
      Ok : Boolean;

   begin
      --  The third argument must be an entity

      Check_Annotate_Entity_Argument (Arg3_Exp, Prag, "Logical_Equal", Ok);
      if not Ok then
         return;
      end if;

      E := Entity (Arg3_Exp);

      --  This entity must be a function

      if Ekind (E) /= E_Function then
         Error_Msg_N_If
           ("Entity parameter of a pragma Logical_Equal must be a function",
            Arg3_Exp);
         return;
      end if;

      --  The function shall have the signature of an equality

      if Number_Formals (E) /= 2 then
         Error_Msg_N_If
           ("Entity parameter of a pragma Logical_Equal shall have exactly"
            & " two parameters",
            E);
         return;
      elsif not Is_Standard_Boolean_Type (Etype (E)) then
         Error_Msg_N_If
           ("Entity parameter of a pragma Logical_Equal shall return a"
            & " Boolean",
            E);
         return;
      elsif Has_Contracts (E, Pragma_Postcondition)
        or else Has_Contracts (E, Pragma_Postcondition, Classwide => True)
      then
         Error_Msg_N_If
           ("Entity parameter of a pragma Logical_Equal shall not have"
            & " post-conditions",
            E);
         return;
      elsif Has_Contracts (E, Pragma_Contract_Cases) then
         Error_Msg_N_If
           ("Entity parameter of a pragma Logical_Equal shall not have"
            & " contract cases",
            E);
         return;
      elsif Has_Aspect (E, Aspect_Potentially_Invalid) then
         Error_Msg_N_If
           ("Entity parameter of a pragma Logical_Equal shall not have"
            & " a Potentially_Invalid aspect",
            E);
         return;
      elsif Potentially_Hidden_Entities.Contains (E) then
         Error_Msg_N_If
           ("a function annotated with Annotate Hide_Info or "
            & "Unhide_Info shall not be a logical equality",
            E);
         return;
      else
         declare
            First_Param : constant Formal_Kind_Id := First_Formal (E);
            Snd_Param   : constant Formal_Kind_Id := Next_Formal (First_Param);
            First_Ty    : constant Type_Kind_Id := Etype (First_Param);
            Snd_Ty      : constant Type_Kind_Id := Etype (Snd_Param);

         begin
            if First_Ty /= Snd_Ty
              and then
                (Ekind (First_Ty) not in E_Anonymous_Access_Type
                 or else Ekind (Snd_Ty) not in E_Anonymous_Access_Type
                 or else
                   Directly_Designated_Type (First_Ty)
                   /= Directly_Designated_Type (Snd_Ty))
            then
               Error_Msg_N_If
                 ("both parameters of an equality function shall have the"
                  & " same subtype",
                  E);
               return;
            end if;
         end;
      end if;

      --  The function shall not access any global data

      declare
         Globals : Global_Flow_Ids;
      begin
         Get_Globals
           (Subprogram          => E,
            Scope               => (Ent => E, Part => Visible_Part),
            Classwide           => False,
            Globals             => Globals,
            Use_Deduced_Globals => not Gnat2Why_Args.Global_Gen_Mode,
            Ignore_Depends      => False);

         if not Globals.Proof_Ins.Is_Empty
           or else not Globals.Inputs.Is_Empty
           or else not Globals.Outputs.Is_Empty
         then
            Error_Msg_N_If
              ("Entity parameter of a pragma Logical_Equal shall not access"
               & " any global data",
               E);
            return;
         end if;
      end;

      --  Inline_For_Proof and Logical_Equal are incompatible

      if Present (Retrieve_Inline_Annotation (E)) then
         Error_Msg_N_If
           ("Entity parameter of a pragma Logical_Equal shall not have an"
            & " Inline_For_Proof annotation",
            Arg3_Exp);
         return;
      end if;

      Check_Annotate_Placement (E, Prag, "Logical_Equal", Ok);
      if not Ok then
         return;
      end if;

      Logical_Eq_Annotations.Include (E);
      Inline_Pragmas.Include (E, Prag);
   end Check_Logical_Equal_Annotation;

   --------------------------------------------
   -- Check_Mutable_In_Parameters_Annotation --
   --------------------------------------------

   procedure Check_Mutable_In_Parameters_Annotation
     (Arg3_Exp : Node_Id; Prag : Node_Id)
   is
      Ok    : Boolean;
      Ent   : Entity_Id;
      Scope : Entity_Id;
   begin
      --  The 4th argument must be an entity

      Check_Annotate_Entity_Argument
        (Arg3_Exp, Prag, "Mutable_In_Parameters", Ok);
      if not Ok then
         return;
      end if;
      Ent := Entity (Arg3_Exp);

      --  Ent shall be a private type whose full view is ultimately either
      --  private or an access-to-variable type. For now, do not allow
      --  tags and discriminants.

      if not Is_Private_Type (Ent) then
         Error_Msg_N_If
           ("Entity parameter of a pragma Annotate ""Mutable_In_Parameters"""
            & " shall be a private type",
            Prag);
         return;

      elsif Has_Discriminants (Retysp (Ent)) then
         Error_Msg_N_If
           ("Entity parameter of a pragma Annotate ""Mutable_In_Parameters"""
            & " shall not have discriminants",
            Prag);
         return;

      elsif Is_Tagged_Type (Retysp (Ent)) then
         Error_Msg_N_If
           ("Entity parameter of a pragma Annotate ""Mutable_In_Parameters"""
            & " shall not be tagged",
            Prag);
         return;

      elsif not Is_Private_Type (Retysp (Ent))
        and then
          not (Is_Access_Type (Retysp (Ent))
               and then Is_Access_Variable (Retysp (Ent)))
      then
         Error_Msg_N_If
           ("the full view of the Entity parameter of a pragma Annotate"
            & " ""Mutable_In_Parameters"" shall either be an"
            & " access-to-variable type or not be visible in SPARK",
            Prag);
         return;
      end if;

      --  Search the node to which the current annotation applies. Look for a
      --  declaration directly before Prag.

      Scope := Annot_Applies_To (Prag, OK_Scope => False, OK_Body => False);

      if No (Scope) or else not Is_Subprogram_Or_Entry (Scope) then
         Error_Msg_N_If
           ("pragma Annotate ""Mutable_In_Parameters"""
            & " must appear just after a subprogram or entry",
            Prag);
         return;

      elsif Ekind (Scope) = E_Function
        and then not Is_Function_With_Side_Effects (Scope)
      then
         Error_Msg_N_If
           ("pragma Annotate ""Mutable_In_Parameters"""
            & " cannot appear after function without side effects",
            Prag);
         return;

      elsif Is_Dispatching_Operation (Scope) then
         Error_Msg_N_If
           ("pragma Annotate ""Mutable_In_Parameters"""
            & " cannot appear after a dispatching operation",
            Prag);
         return;

      elsif Has_Automatic_Instantiation_Annotation (Scope) then
         Error_Msg_N_If
           ("pragma Annotate ""Mutable_In_Parameters"""
            & " cannot appear after an automatically instantiated lemma",
            Prag);
         return;
      elsif Has_Depends (Scope) then
         Error_Msg_N_If
           ("pragma Annotate ""Mutable_In_Parameters"""
            & " cannot appear after a subprogram with ""Depends"" contract",
            Prag);
      end if;

      declare
         Formal : Entity_Id := First_Formal (Scope);
         Found  : Boolean := False;
      begin
         while Present (Formal) loop
            if Ekind (Formal) = E_In_Parameter
              and then Retysp (Etype (Formal)) = Retysp (Ent)
            then
               Found := True;
               exit;
            end if;
            Next_Formal (Formal);
         end loop;

         if not Found then
            Error_Msg_N_If
              (Pretty_Source_Name (Scope)
               & " does not have any ""in"" parameter of "
               & Pretty_Source_Name (Ent),
               Prag);
            return;
         end if;
      end;

      --  Update the Mutable_In_Params_Annotations map

      declare
         Position : Node_Graphs.Cursor;
         Inserted : Boolean;
      begin
         Mutable_In_Params_Annotations.Insert
           (Scope, Node_Sets.Empty_Set, Position, Inserted);
         Mutable_In_Params_Annotations (Position).Include (Retysp (Ent));
      end;
   end Check_Mutable_In_Parameters_Annotation;

   --------------------------------------------
   -- Check_No_Bitwise_Operations_Annotation --
   --------------------------------------------

   procedure Check_No_Bitwise_Operations_Annotation
     (Arg3_Exp : Node_Id; Prag : Node_Id)
   is
      E    : Entity_Id;
      Decl : Node_Id;
      Base : Entity_Id;
      Ok   : Boolean;

   begin
      Check_Annotate_Entity_Argument
        (Arg3_Exp, Prag, "No_Bitwise_Operations", Ok);
      if not Ok then
         return;
      end if;

      E := Entity (Arg3_Exp);
      if Present (Full_View (E)) then
         E := Full_View (E);
      end if;
      Decl := Parent (E);

      --  Annotation should apply to type declaration (not subtype)

      if Nkind (Decl) /= N_Full_Type_Declaration then
         Error_Msg_N_If
           ("Annotation No_Bitwise_Operations must apply"
            & " to a type declaration",
            Arg3_Exp);
         return;

      --  This entity must be a modular type

      elsif not Has_Modular_Operations (E) then
         Error_Msg_N_If
           ("Entity parameter of annotation No_Bitwise_Operations must"
            & " be a modular type",
            Arg3_Exp);
         return;
      end if;

      --  Annotation may apply to a (derived) type declaration. In case of
      --  derivation, retrieve the base type.

      if Ekind (E) = E_Modular_Integer_Type then
         Base := E;
      else
         Base := Etype (E);
      end if;
      pragma Assert (Ekind (Base) = E_Modular_Integer_Type);

      Check_Annotate_Placement
        (E,
         Placed_At_Full_View,
         Prag,
         "No_Bitwise_Operations",
         "full type declaration of " & Pretty_Source_Name (E),
         Ok);
      if not Ok then
         return;
      end if;

      Set_Has_No_Bitwise_Operations_Annotation (Base);
   end Check_No_Bitwise_Operations_Annotation;

   -------------------------------------
   -- Check_No_Wrap_Around_Annotation --
   -------------------------------------

   procedure Check_No_Wrap_Around_Annotation
     (Arg3_Exp : Node_Id; Prag : Node_Id)
   is
      E    : Entity_Id;
      Decl : Node_Id;
      Base : Entity_Id;
      Ok   : Boolean;

   begin
      Check_Annotate_Entity_Argument (Arg3_Exp, Prag, "No_Wrap_Around", Ok);
      if not Ok then
         return;
      end if;

      E := Entity (Arg3_Exp);
      if Present (Full_View (E)) then
         E := Full_View (E);
      end if;
      Decl := Parent (E);

      --  Annotation should apply to type declaration (not subtype)

      if Nkind (Decl) /= N_Full_Type_Declaration then
         Error_Msg_N_If
           ("Annotation No_Wrap_Around must apply to a type declaration",
            Arg3_Exp);
         return;

      --  This entity must be a modular type

      elsif not Has_Modular_Operations (E) then
         Error_Msg_N_If
           ("Entity parameter of annotation No_Wrap_Around must be a modular "
            & "type",
            Arg3_Exp);
         return;
      end if;

      --  Annotation may apply to a (derived) type declaration. In case of
      --  derivation, retrieve the base type.

      if Ekind (E) = E_Modular_Integer_Type then
         Base := E;
      else
         Base := Etype (E);
      end if;
      pragma Assert (Ekind (Base) = E_Modular_Integer_Type);

      Check_Annotate_Placement
        (E,
         Placed_At_Full_View,
         Prag,
         "No_Wrap_Around",
         "full type declaration of " & Pretty_Source_Name (E),
         Ok);
      if not Ok then
         return;
      end if;

      Set_Has_No_Wrap_Around_Annotation (Base);
   end Check_No_Wrap_Around_Annotation;

   --------------------------------
   -- Check_Ownership_Annotation --
   --------------------------------

   procedure Check_Ownership_Annotation
     (Aspect_Or_Pragma : String;
      Arg3_Exp         : Node_Id;
      Arg4_Exp         : Node_Id;
      Prag             : Node_Id)
   is
      From_Aspect : constant Boolean := From_Aspect_Specification (Prag);
      Last_Exp    : constant Node_Id :=
        (if No (Arg4_Exp) then Arg3_Exp else Arg4_Exp);
      Extra_Exp   : constant Node_Id :=
        (if No (Arg4_Exp) then Empty else Arg3_Exp);
      Ok          : Boolean;

   begin
      --  The last argument must be an entity

      Check_Annotate_Entity_Argument
        (Last_Exp, Prag, "Ownership", Ok, Ignore_SPARK_Status => True);
      --  It would be fine to take SPARK status into account for type case,
      --    but not in function case.
      if not Ok then
         return;
      end if;

      --  The extra argument if any must be a string literal

      if Present (Extra_Exp) and then Nkind (Extra_Exp) not in N_String_Literal
      then
         Mark_Incorrect_Use_Of_Annotation
           (Annot_String_Third_Argument,
            Arg3_Exp,
            Name        => "Ownership",
            From_Aspect => From_Aspect);
         return;
      end if;

      declare
         Ent                    : constant Entity_Id := Entity (Last_Exp);
         Kind                   : constant String :=
           (if No (Extra_Exp)
            then ""
            else To_Lower (To_String (Strval (Extra_Exp))));
         Needs_Reclamation_Cont : constant Message :=
           Create
             ("consider annotating it with a pragma Annotate "
              & "(GNATprove, Ownership,"
              & " ""Needs_Reclamation"", ...)");
      begin
         if Ekind (Ent) in Type_Kind then

            if not In_SPARK (Ent) then
               return;
            --  Annotation Irrelevant if type not in SPARK

            end if;

            --  Check that the entity is a private type whose whose full view
            --  has SPARK_Mode => Off.

            if Ekind (Ent)
               not in E_Private_Type
                    | E_Record_Type_With_Private
                    | E_Limited_Private_Type
              or else Parent_Type (Ent) /= Ent
            then
               Error_Msg_N_If
                 ("a type annotated with Ownership must be a private type",
                  Ent);

            elsif Retysp (Ent) /= Ent
              and then not Has_Hidden_Private_Part (Scope (Ent))
            then
               Error_Msg_N_If
                 ("the private part of the scope of a private type annotated "
                  & "with Ownership must have either a pragma SPARK_Mode "
                  & "(Off) or a Hide_Info annotation",
                  Ent);

            --  pragma Annotate (GNATprove, Ownership, Ent);
            --  or else
            --  pragma Annotate (GNATprove, Ownership, Needs_Reclamation, Ent);

            elsif No (Extra_Exp) or else Kind = "needs_reclamation" then
               Check_Annotate_Placement
                 (Ent,
                  Placed_At_Private_View,
                  Prag,
                  "Ownership",
                  " private declaration of " & Pretty_Source_Name (Ent),
                  Ok);
               if not Ok then
                  return;
               end if;

               --  The full view of Ent is visible, check that the annotation
               --  is a confirming annotation. We do not return early in case
               --  of violations to avoid spurious error messages about missing
               --  annotations on the partial views.

               if Retysp (Ent) /= Ent then
                  pragma Assert (Has_Hidden_Private_Part (Scope (Ent)));

                  declare
                     Dummy       : Unbounded_String;
                     Full_Ty     : constant Entity_Id := Retysp (Ent);
                     Reclamation : constant Boolean := Present (Extra_Exp);
                  begin
                     if Has_Ownership_Annotation (Full_Ty) then
                        if Needs_Reclamation (Full_Ty) /= Reclamation then
                           Error_Msg_N_If
                             ("full view of type annotated with an "
                              & "Ownership annotation "
                              & "shall have a matching annotation",
                              Full_Ty);
                        end if;

                     elsif not Is_Deep (Full_Ty) then
                        Error_Msg_N_If
                          ("full view of type annotated with an Ownership "
                           & "annotation shall be subject to ownership",
                           Full_Ty);

                     elsif Reclamation
                       and then not Contains_Allocated_Parts (Full_Ty)
                     then
                        Error_Msg_N_If
                          ("full view of type annotated with "
                           & """Needs_Reclamation"" shall need reclamation",
                           Full_Ty);

                     elsif not Reclamation
                       and then Contains_Allocated_Parts (Full_Ty)
                     then
                        Error_Msg_N_If
                          ("full view of type annotated with an Ownership "
                           & "annotation without ""Needs_Reclamation"" shall "
                           & "not need reclamation",
                           Full_Ty);
                     end if;
                  end;
               end if;

               declare
                  Confirming : constant Boolean := Retysp (Ent) /= Ent;
                  Position   : Node_To_Ownership_Maps.Cursor;
               begin
                  Ownership_Annotations.Insert
                    (Retysp (Ent),
                     (if No (Extra_Exp)
                      then
                        (Needs_Reclamation => False, Confirming => Confirming)
                      else
                        (Needs_Reclamation => True,
                         Confirming        => Confirming,
                         others            => <>)),
                     Position,
                     Ok);
                  if not Ok then
                     Error_Msg_N_If
                       ("type shall not have multiple ownership "
                        & "annotations",
                        Ent);
                  end if;
               end;

            --  Nothing else is allowed

            else
               Error_Msg_N_If
                 ("third argument of "
                  & Aspect_Or_Pragma
                  & " Annotate Ownership on a type must be"
                  & " ""Needs_Reclamation""",
                  Extra_Exp);
            end if;

         elsif Ekind (Ent) = E_Function then

            --  Check that an extra parameter is provided

            if No (Extra_Exp) then
               Error_Msg_N_If
                 ("third argument of "
                  & Aspect_Or_Pragma
                  & " Annotate Ownership on a"
                  & " function must be either ""Needs_Reclamation"""
                  & " or ""Is_Reclaimed""",
                  Last_Exp);

            --  Check that the function returns a boolean

            elsif Etype (Ent) /= Standard_Boolean then
               Error_Msg_N_If
                 ("a function annotated with Ownership must return a boolean",
                  Ent);

            --  Check that the function has only one parameter

            elsif Number_Formals (Ent) /= 1 then
               Error_Msg_N_If
                 ("a function annotated with Ownership must "
                  & "have exactly one formal parameter",
                  Ent);

            else

               --  Annotation for a type that is not in SPARK is irrelevant.

               if not In_SPARK (Etype (First_Formal (Ent))) then
                  return;
               end if;

               --  Function must be in SPARK.

               if not In_SPARK (Ent) then
                  Mark_Violation (Last_Exp, From => Ent);
                  return;
               end if;

               declare
                  P_Typ   : constant Entity_Id := Etype (First_Formal (Ent));
                  G_Typ   : constant Entity_Id := Retysp (P_Typ);
                  Typ     : constant Entity_Id :=
                    (if Is_Class_Wide_Type (G_Typ)
                     then Retysp (Get_Specific_Type_From_Classwide (G_Typ))
                     else G_Typ);
                  Globals : Global_Flow_Ids;

               begin
                  --  The function shall not access any global data

                  Get_Globals
                    (Subprogram          => Ent,
                     Scope               => (Ent => Ent, Part => Visible_Part),
                     Classwide           => False,
                     Globals             => Globals,
                     Use_Deduced_Globals => not Gnat2Why_Args.Global_Gen_Mode,
                     Ignore_Depends      => False);

                  if not Globals.Proof_Ins.Is_Empty
                    or else not Globals.Inputs.Is_Empty
                    or else not Globals.Outputs.Is_Empty
                  then
                     Error_Msg_N_If
                       ("a function annotated with Ownership shall"
                        & " not access any global data",
                        Ent);

                  elsif Is_Tagged_Type (Typ)
                    and then not Is_Class_Wide_Type (G_Typ)
                  then
                     Error_Msg_N_If
                       ("function annotated with Ownership on a tagged type "
                        & "expects a classwide type",
                        Ent);

                  elsif not Ownership_Annotations.Contains (Typ) then
                     Error_Msg_N_If
                       ("the type of the first parameter of a function "
                        & "annotated with Ownership must be annotated with"
                        & " Ownership",
                        Ent,
                        Continuations => [Needs_Reclamation_Cont]);

                  elsif not Ownership_Annotations (Typ).Needs_Reclamation then
                     Error_Msg_N_If
                       ("the type of the first parameter of a function "
                        & "annotated with Ownership shall need reclamation",
                        Ent,
                        Continuations => [Needs_Reclamation_Cont]);

                  elsif Present
                          (Ownership_Annotations (Typ).Reclamation_Entity)
                  then
                     Error_Msg_N_If
                       ("a single ownership function or constant shall be"
                        & " supplied for a given type annotated with"
                        & " Ownership",
                        Ent,
                        Continuations =>
                          [Create
                             ("& conflicts with the current annotation",
                              Names =>
                                [Ownership_Annotations (Typ)
                                   .Reclamation_Entity])]);

                  elsif List_Containing (Parent (P_Typ))
                    /= List_Containing (Prag)
                  then
                     Error_Msg_N_If
                       ("ownership function shall be declared in same "
                        & "declaration list as input type",
                        Ent);

                  --  pragma Annotate
                  --   (GNATprove, Ownership, Needs_Reclamation, Ent);
                  --  or else
                  --  pragma Annotate
                  --   (GNATprove, Ownership, Is_Reclaimed, Ent);

                  elsif Kind = "needs_reclamation"
                    or else Kind = "is_reclaimed"
                  then

                     --  Check placement. No good solution here.

                     Check_Annotate_Placement (Ent, Prag, "Ownership", Ok);
                     if not Ok then
                        return;
                     end if;

                     Ownership_Annotations (Typ).Reclamation_Entity := Ent;
                     Ownership_Annotations (Typ).Reclaimed :=
                       (if Kind = "is_reclaimed"
                        then Is_Reclaimed
                        else Needs_Reclamation);

                  --  Nothing else is allowed

                  else
                     Error_Msg_N_If
                       ("third argument of "
                        & Aspect_Or_Pragma
                        & " Annotate Ownership on a"
                        & " function must be either ""Needs_Reclamation"""
                        & " or ""Is_Reclaimed""",
                        Extra_Exp);
                  end if;
               end;
            end if;

         elsif Ekind (Ent) = E_Constant then

            --  Check that an extra parameter is provided

            if No (Extra_Exp) then
               Error_Msg_N_If
                 ("third argument of "
                  & Aspect_Or_Pragma
                  & " Annotate Ownership on a"
                  & " constant must be ""Reclaimed_Value""",
                  Last_Exp);

            else
               --  Annotation for a type that is not in SPARK is irrelevant

               if not In_SPARK (Etype (Ent)) then
                  return;
               end if;

               --  Constant must be in SPARK

               if not In_SPARK (Ent) then
                  Mark_Violation (Last_Exp, From => Ent);
                  return;
               end if;

               declare
                  Typ : constant Entity_Id := Retysp (Etype (Ent));
               begin
                  if not Ownership_Annotations.Contains (Typ) then
                     Error_Msg_N_If
                       ("the type of a constant annotated with Ownership must"
                        & " be annotated with Ownership",
                        Ent,
                        Continuations => [Needs_Reclamation_Cont]);

                  elsif not Ownership_Annotations (Typ).Needs_Reclamation then
                     Error_Msg_N_If
                       ("the type of a constant annotated with Ownership shall"
                        & " need reclamation",
                        Ent,
                        Continuations => [Needs_Reclamation_Cont]);

                  elsif Is_Tagged_Type (Typ) then
                     Error_Msg_N_If
                       ("constant annotated with Ownership cannot be used on"
                        & " a tagged type",
                        Ent,
                        Continuations =>
                          [Create ("use a reclamation function instead")]);

                  elsif Present
                          (Ownership_Annotations (Typ).Reclamation_Entity)
                  then
                     Error_Msg_N_If
                       ("a single ownership function or constant shall be"
                        & " supplied for a given type annotated with"
                        & " Ownership",
                        Ent,
                        Continuations =>
                          [Create
                             ("& conflicts with the current annotation",
                              Names =>
                                [Ownership_Annotations (Typ)
                                   .Reclamation_Entity])]);

                  elsif List_Containing (Parent (Etype (Ent)))
                    /= List_Containing (Prag)
                  then
                     Error_Msg_N_If
                       ("constant annotated with ownership shall be declared "
                        & "in same declaration list as its type",
                        Ent);

                  --  pragma Annotate
                  --   (GNATprove, Ownership, "Reclaimed_Value", Ent);

                  elsif Kind = "reclaimed_value" then

                     --  Check placement

                     Check_Annotate_Placement (Ent, Prag, "Ownership", Ok);
                     if not Ok then
                        return;
                     end if;

                     Ownership_Annotations (Typ).Reclamation_Entity := Ent;
                     Ownership_Annotations (Typ).Reclaimed := Reclaimed_Value;

                  --  Nothing else is allowed

                  else
                     Error_Msg_N_If
                       ("third argument of "
                        & Aspect_Or_Pragma
                        & " Annotate Ownership on a"
                        & " constant must be ""Reclaimed_Value""",
                        Extra_Exp);
                  end if;
               end;
            end if;
         else
            Error_Msg_N_If
              ("the entity of a pragma Annotate Ownership "
               & "shall be either a type, a constant, or a function",
               Ent);
         end if;
      end;
   end Check_Ownership_Annotation;

   ------------------------------------
   -- Check_Predefined_Eq_Annotation --
   ------------------------------------

   procedure Check_Predefined_Eq_Annotation
     (Aspect_Or_Pragma : String;
      Arg3_Exp         : Node_Id;
      Arg4_Exp         : Node_Id;
      Prag             : Node_Id)
   is
      From_Aspect : constant Boolean := From_Aspect_Specification (Prag);
      Ok          : Boolean;

   begin
      --  The last argument must be an entity

      Check_Annotate_Entity_Argument
        (Arg4_Exp,
         Prag,
         "Predefined_Equality",
         Ok,
         Ignore_SPARK_Status => True);

      --  Annotation for a type or constant that is not in SPARK is
      --  irrelevant.

      if not Ok or else not In_SPARK (Entity (Arg4_Exp)) then
         return;
      end if;

      --  The extra argument if any must be a string literal

      if Present (Arg3_Exp) and then Nkind (Arg3_Exp) not in N_String_Literal
      then
         Mark_Incorrect_Use_Of_Annotation
           (Annot_String_Third_Argument,
            Arg3_Exp,
            Name        => "Predefined_Equaliy",
            From_Aspect => From_Aspect);
         return;
      end if;

      declare
         Ent  : constant Entity_Id := Entity (Arg4_Exp);
         Kind : constant String := To_Lower (To_String (Strval (Arg3_Exp)));

      begin
         if Ekind (Ent) in Type_Kind then

            --  Check that the entity is a private type whose whose full view
            --  has SPARK_Mode => Off.

            if Ekind (Ent)
               not in E_Private_Type
                    | E_Record_Type_With_Private
                    | E_Limited_Private_Type
              or else Parent_Type (Ent) /= Ent
            then
               Error_Msg_N_If
                 ("a type annotated with Predefined_Equality must be"
                  & " a private type",
                  Ent);

            elsif Retysp (Ent) /= Ent
              and then not Has_Hidden_Private_Part (Scope (Ent))
            then
               Error_Msg_N_If
                 ("the private part of the scope of a type annotated with "
                  & "Predefined_Equality must have either a pragma SPARK_Mode "
                  & "(Off) or a Hide_Info annotation",
                  Ent);

            --  For now, we only support:
            --
            --  pragma Annotate
            --    (GNATprove, Predefined_Equality, "Only_Null", Ent);
            --  pragma Annotate
            --    (GNATprove, Predefined_Equality, "No_Equality", Ent);

            elsif Kind not in "only_null" | "no_equality" then

               Error_Msg_N_If
                 ("third argument of "
                  & Aspect_Or_Pragma
                  & " Annotate Predefined_Equality on a type must be"
                  & " either ""Only_Null"" or ""No_Equality""",
                  Arg3_Exp);

            --  Only null is not supported on tagged types as contants are
            --  not well suited for inheritance.

            elsif Kind = "only_null" and then Is_Tagged_Type (Ent) then
               Error_Msg_N_If
                 ("a tagged type cannot be annotated with ""Only_Null""", Ent);

            else
               Check_Annotate_Placement
                 (Ent,
                  Placed_At_Private_View,
                  Prag,
                  "Predefined_Equality",
                  " private declaration of " & Pretty_Source_Name (Ent),
                  Ok);

               if not Ok then
                  return;
               end if;

               --  The full view of Ent is visible, check that the annotation
               --  is a confirming annotation. We do not return early in case
               --  of violations to avoid spurious error messages about missing
               --  annotations on the partial views.

               if Retysp (Ent) /= Ent then
                  pragma Assert (Has_Hidden_Private_Part (Scope (Ent)));

                  declare
                     Dummy    : Opt_Type_Kind_Id;
                     Full_Ty  : constant Entity_Id := Retysp (Ent);
                     Exp_Kind : constant Predefined_Eq_Kind :=
                       (if Kind = "only_null" then Only_Null else No_Equality);
                  begin
                     if Has_Predefined_Eq_Annotation (Full_Ty) then
                        if Get_Predefined_Eq_Kind (Full_Ty) /= Exp_Kind then
                           Error_Msg_N_If
                             ("full view of type annotated with a "
                              & "Predefined_Equality annotation "
                              & "shall have a matching annotation",
                              Full_Ty);
                        end if;
                     elsif Exp_Kind = Only_Null
                       and then not Is_Access_Type (Full_Ty)
                     then
                        Error_Msg_N_If
                          ("full view of type annotated with a "
                           & "Predefined_Equality ""Only_Null"" annotation "
                           & "shall be an access type",
                           Full_Ty);

                     elsif Exp_Kind = No_Equality
                       and then
                         (Is_Access_Type (Full_Ty)
                          or else
                            not Predefined_Eq_Uses_Pointer_Eq (Full_Ty, Dummy))
                     then
                        Error_Msg_N_If
                          ("full view of type annotated with a "
                           & "Predefined_Equality ""No_Equality"" annotation "
                           & "shall be a composite type whose components have "
                           & "a restricted equality",
                           Full_Ty);
                     end if;
                  end;
               end if;

               --  Store the annotation in the map

               declare
                  Position   : Node_To_Predefined_Eq_Maps.Cursor;
                  Confirming : constant Boolean := Retysp (Ent) /= Ent;
                  New_Value  : constant Predefined_Eq_Annotation :=
                    (if Kind = "only_null"
                     then
                       (Kind       => Only_Null,
                        Confirming => Confirming,
                        others     => <>)
                     else (Kind => No_Equality, Confirming => Confirming));
               begin
                  Predefined_Eq_Annotations.Insert
                    (Retysp (Ent), New_Value, Position, Ok);
                  if not Ok then
                     Error_Msg_N_If
                       ("type shall not have multiple "
                        & "Predefined_Equality annotations",
                        Ent);
                  end if;
               end;
            end if;

         elsif Ekind (Ent) = E_Constant then

            declare
               Typ            : constant Entity_Id := Retysp (Etype (Ent));
               Only_Null_Cont : constant Message :=
                 Create
                   ("consider annotating it with a pragma Annotate "
                    & "(GNATprove, Predefined_Equality, ""Only_Null"""
                    & ", ...)");
            begin
               --  pragma Annotate
               --   (GNATprove, Predefined_Equality, "Null_Value", Ent);

               if Kind /= "null_value" then
                  Error_Msg_N_If
                    ("third argument of "
                     & Aspect_Or_Pragma
                     & " Annotate Predefined_Equality on a"
                     & " constant must be ""Null_Value""",
                     Arg3_Exp);

               elsif not Predefined_Eq_Annotations.Contains (Typ) then
                  Error_Msg_N_If
                    ("the type of a constant annotated with"
                     & " Predefined_Equality must be annotated with "
                     & "Predefined_Equality",
                     Ent,
                     Continuations => [Only_Null_Cont]);

               elsif Predefined_Eq_Annotations (Typ).Kind /= Only_Null then
                  Error_Msg_N_If
                    ("the type of a constant annotated with"
                     & " Predefined_Equality must be annotated with "
                     & """Only_Null""",
                     Ent,
                     Continuations => [Only_Null_Cont]);

               elsif Predefined_Eq_Annotations (Typ).Null_Value = Ent then
                  Error_Msg_N_If
                    ("constant shall not have multiple "
                     & "Predefined_Equality annotations",
                     Ent);

               elsif Present (Predefined_Eq_Annotations (Typ).Null_Value) then
                  Error_Msg_N_If
                    ("a single null value shall be supplied for a given type "
                     & "annotated with Predefined_Equality",
                     Ent,
                     Continuations =>
                       [Create
                          ("& conflicts with the current annotation",
                           Names =>
                             [Predefined_Eq_Annotations (Typ).Null_Value])]);
               elsif List_Containing (Parent (Etype (Ent)))
                 /= List_Containing (Prag)
               then
                  Error_Msg_N_If
                    ("constant annotated with Predefined_Equality shall be "
                     & "declared in same declaration list as its type",
                     Ent);

               else
                  --  Check placement

                  Check_Annotate_Placement
                    (Ent, Prag, "Predefined_Equality", Ok);

                  if not Ok then
                     return;
                  end if;

                  --  For confirming annotations, we need to check that the
                  --  value of the constant is a null value. Delay the check
                  --  to be sure the full view is marked.

                  if Predefined_Eq_Annotations (Typ).Confirming then
                     Delayed_Null_Values.Append (Ent);
                  end if;

                  --  Update the Predefined_Eq_Annotations map

                  Predefined_Eq_Annotations (Typ).Null_Value := Ent;
               end if;
            end;
         else
            Error_Msg_N_If
              ("the entity of a pragma Annotate Predefined_Equality "
               & "shall be either a type or a constant",
               Ent);
         end if;
      end;
   end Check_Predefined_Eq_Annotation;

   ---------------------------------------
   -- Decl_Starts_Pragma_Annotate_Range --
   ---------------------------------------

   function Decl_Starts_Pragma_Annotate_Range (N : Node_Id) return Boolean
   is (Comes_From_Source (N)
       or else
         (Is_Rewrite_Substitution (N)
          and then Comes_From_Source (Original_Node (N)))
       or else
         (Nkind (N) in N_Subprogram_Declaration
          and then Is_Generic_Instance (Defining_Entity (N))
          and then
            Comes_From_Source
              (Sem_Ch12.Get_Unit_Instantiation_Node
                 (Defining_Entity (Parent (N))))));

   --------------------------------------
   -- Do_Delayed_Checks_For_Aggregates --
   --------------------------------------

   procedure Do_Delayed_Checks_For_Aggregates (Typ : Entity_Id) is

      P_Typ    : constant Entity_Id :=
        (if Is_Full_View (Typ) then Partial_View (Typ) else Typ);
      Typ_List : constant List_Id := List_Containing (Parent (P_Typ));
      Annot    : Aggregate_Annotation renames Aggregate_Annotations (Typ);

   begin
      --  Search for an applicable Capacity function. It is optional.

      declare
         use Delayed_Aggregate_Function_Maps;
         Position : constant Delayed_Aggregate_Function_Maps.Cursor :=
           Delayed_Capacity.Find
             ((Enclosing_List      => Typ_List,
               Base_Component_Type => Types.Empty));
      begin
         if Has_Element (Position) then
            if Present (Annot.Spec_Capacity) then
               Error_Msg_NE_If
                 ("""Capacity"" function for & shall take the container "
                  & "as a parameter",
                  Element (Position),
                  Typ,
                  Continuations =>
                    [Create
                       ("& takes the capacity as a parameter",
                        Names => [Annot.Empty_Function])]);
            else
               Annot.Capacity := Element (Position);
            end if;
         end if;
      end;

      case Annot.Kind is
         when Sets   =>

            --  Search for an applicable Equivalent_Elements function. It is
            --  mandatory.

            declare
               use Delayed_Aggregate_Function_Maps;
               Position : constant Delayed_Aggregate_Function_Maps.Cursor :=
                 Delayed_Equivalent_Elements.Find
                   ((Enclosing_List      => Typ_List,
                     Base_Component_Type => Base_Type (Annot.Element_Type)));
            begin
               if Has_Element (Position) then
                  Annot.Equivalent_Elements := Element (Position);
               else
                  Error_Msg_NE_If
                    ("no ""Equivalent_Elements"" function found for type "
                     & "with predefined set aggregates &",
                     Typ,
                     Typ);
               end if;
            end;

            --  Contains function is mandatory

            if No (Annot.Contains) then
               Error_Msg_NE_If
                 ("no ""Contains"" function found for type with "
                  & "predefined set aggregates &",
                  Typ,
                  Typ);
            end if;

            --  Length is optional

            if No (Annot.Sets_Length) and then Emit_Warning_Info_Messages then
               Warning_Msg_N_If
                 (Warn_Set_Length_Aggregates,
                  Typ,
                  Continuations =>
                    [Create
                       ("the cardinality of aggregates will be unknown")]);
            end if;

         when Maps   =>

            --  Search for applicable Equivalent_Keys and Default_Item
            --  functions. Equivalent_Keys is mandatory.

            declare
               use Delayed_Aggregate_Function_Maps;
               Position : constant Delayed_Aggregate_Function_Maps.Cursor :=
                 Delayed_Equivalent_Keys.Find
                   ((Enclosing_List      => Typ_List,
                     Base_Component_Type => Base_Type (Annot.Key_Type)));
            begin
               if Has_Element (Position) then
                  Annot.Equivalent_Keys := Element (Position);
               else
                  Error_Msg_NE_If
                    ("no ""Equivalent_Keys"" function found for type "
                     & "with predefined map aggregates &",
                     Typ,
                     Typ);
               end if;
            end;

            declare
               use Delayed_Aggregate_Function_Maps;
               Position : constant Delayed_Aggregate_Function_Maps.Cursor :=
                 Delayed_Default_Item.Find
                   ((Enclosing_List      => Typ_List,
                     Base_Component_Type => Base_Type (Annot.Element_Type)));
            begin
               if Has_Element (Position) then
                  Annot.Default_Item := Element (Position);
               end if;
            end;

            --  Has_Key and Default_Item are exclusive, exactly one should be
            --  supplied.

            if No (Annot.Has_Key) and then No (Annot.Default_Item) then
               Error_Msg_NE_If
                 ("no ""Has_Key"" nor ""Default_Item"" function found "
                  & "for type with predefined map aggregates &",
                  Typ,
                  Typ);
            end if;

            if Present (Annot.Has_Key) and then Present (Annot.Default_Item)
            then
               Error_Msg_NE_If
                 ("""Has_Key"" and ""Default_Item"" functions shall "
                  & "not both be specified for type with predefined map"
                  & " aggregates &",
                  Typ,
                  Typ);
            end if;

            --  Get is mandatory

            if No (Annot.Maps_Get) then
               Error_Msg_NE_If
                 ("no ""Get"" function found for type "
                  & "with predefined map aggregates &",
                  Typ,
                  Typ);
            end if;

            --  Length is optional. It can only be supplied for partial maps
            --  (with Has_Key and not Default_Item).

            if Present (Annot.Maps_Length)
              and then Present (Annot.Default_Item)
            then
               Error_Msg_NE_If
                 ("""Length"" and ""Default_Item"" functions shall "
                  & "not both be specified for type with predefined map"
                  & " aggregates &",
                  Typ,
                  Typ);
            end if;

            if No (Annot.Maps_Length)
              and then Present (Annot.Has_Key)
              and then Emit_Warning_Info_Messages
            then
               Warning_Msg_N_If
                 (Warn_Map_Length_Aggregates,
                  Typ,
                  Continuations =>
                    [Create
                       ("the cardinality of aggregates will be unknown")]);
            end if;

         when Seqs   =>

            --  Search for an applicable First function. It is mandatory.

            if Present (Annot.Index_Type) then
               declare
                  use Delayed_Aggregate_Function_Maps;
                  Position : constant Delayed_Aggregate_Function_Maps.Cursor :=
                    Delayed_First.Find
                      ((Enclosing_List      => Typ_List,
                        Base_Component_Type => Annot.Index_Type));
               begin
                  if Has_Element (Position) then
                     Annot.First := Element (Position);
                  else
                     Error_Msg_NE_If
                       ("no ""First"" function found for type "
                        & "with predefined set aggregates &",
                        Typ,
                        Typ);
                  end if;
               end;
            end if;

            --  Last and Get functions are mandatory

            if No (Annot.Last) then
               Error_Msg_NE_If
                 ("no ""Last"" function found for type "
                  & "with predefined sequence aggregates &",
                  Typ,
                  Typ);

            --  Reset the index type to the return type of Last. It will be
            --  useful to determine the last possible index if any.

            else
               Annot.Index_Type := Etype (Annot.Last);
            end if;

            if No (Annot.Seqs_Get) then
               Error_Msg_NE_If
                 ("no ""Get"" function found for type "
                  & "with predefined sequence aggregates &",
                  Typ,
                  Typ);
            end if;

         when others =>

            --  Model function is mandatory

            if No (Annot.Model) then
               Error_Msg_NE_If
                 ("no ""Model"" function found for type "
                  & "with aggregates using models &",
                  Typ,
                  Typ);
            else

               --  Check that container aggregates on the
               --  source and the target match.

               declare
                  Source_Asp            : constant Node_Id :=
                    Find_Aggregate_Aspect (Typ);
                  Source_Empty          : Node_Id := Empty;
                  Source_Add_Named      : Node_Id := Empty;
                  Source_Add_Unnamed    : Node_Id := Empty;
                  Source_New_Indexed    : Node_Id := Empty;
                  Source_Assign_Indexed : Node_Id := Empty;

                  Target_Asp            : constant Node_Id :=
                    Find_Aggregate_Aspect (Etype (Annot.Model));
                  Target_Empty          : Node_Id := Empty;
                  Target_Add_Named      : Node_Id := Empty;
                  Target_Add_Unnamed    : Node_Id := Empty;
                  Target_New_Indexed    : Node_Id := Empty;
                  Target_Assign_Indexed : Node_Id := Empty;

                  Source_Add      : Entity_Id;
                  Source_C_Formal : Node_Id;
                  Source_E_Formal : Node_Id;
                  Source_K_Formal : Node_Id := Empty;

                  Target_Add      : Entity_Id;
                  Target_C_Formal : Node_Id;
                  Target_E_Formal : Node_Id;
                  Target_K_Formal : Node_Id := Empty;

                  Error_Msg : constant String :=
                    "concrete and model types of a ""Model"" "
                    & "function shall define compatible "
                    & "aggregates";

               begin
                  Parse_Aspect_Aggregate
                    (N                   => Source_Asp,
                     Empty_Subp          => Source_Empty,
                     Add_Named_Subp      => Source_Add_Named,
                     Add_Unnamed_Subp    => Source_Add_Unnamed,
                     New_Indexed_Subp    => Source_New_Indexed,
                     Assign_Indexed_Subp => Source_Assign_Indexed);

                  Parse_Aspect_Aggregate
                    (N                   => Target_Asp,
                     Empty_Subp          => Target_Empty,
                     Add_Named_Subp      => Target_Add_Named,
                     Add_Unnamed_Subp    => Target_Add_Unnamed,
                     New_Indexed_Subp    => Target_New_Indexed,
                     Assign_Indexed_Subp => Target_Assign_Indexed);

                  if Present (Source_Add_Named) /= Present (Target_Add_Named)
                  then
                     Error_Msg_N_If (Error_Msg, Annot.Model);
                     return;
                  elsif Present (Source_Add_Named) then
                     Source_Add := Entity (Source_Add_Named);
                     Target_Add := Entity (Target_Add_Named);
                  else
                     Source_Add := Entity (Source_Add_Unnamed);
                     Target_Add := Entity (Target_Add_Unnamed);
                  end if;

                  --  Retrieve the formals and check their
                  --  types.

                  Source_C_Formal := First_Formal (Source_Add);
                  Target_C_Formal := First_Formal (Target_Add);

                  if Present (Source_Add_Named) then
                     Source_K_Formal := Next_Formal (Source_C_Formal);
                     Target_K_Formal := Next_Formal (Target_C_Formal);
                     Source_E_Formal := Next_Formal (Source_K_Formal);
                     Target_E_Formal := Next_Formal (Target_K_Formal);
                  else
                     Source_E_Formal := Next_Formal (Source_C_Formal);
                     Target_E_Formal := Next_Formal (Target_C_Formal);
                  end if;

                  if Retysp (Etype (Source_E_Formal))
                    /= Retysp (Etype (Target_E_Formal))
                  then
                     Error_Msg_N_If
                       (Error_Msg & ", element types do not match",
                        Annot.Model);
                     return;
                  elsif Present (Source_Add_Named)
                    and then
                      Retysp (Etype (Source_K_Formal))
                      /= Retysp (Etype (Target_K_Formal))
                  then
                     Error_Msg_N_If
                       (Error_Msg & ", key types do not match", Annot.Model);
                     return;
                  end if;
               end;
            end if;

            --  Check that the capacity function inherited from the model is
            --  compatible if any.

            if No (Annot.Capacity) then
               declare
                  Model_Type    : Entity_Id;
                  Current_Annot : Aggregate_Annotation := Annot;
               begin
                  while Current_Annot.Kind = Model
                    and then Present (Current_Annot.Model)
                  loop
                     Model_Type := Current_Annot.Model_Type;
                     Current_Annot := Get_Aggregate_Annotation (Model_Type);

                     if Present (Current_Annot.Capacity) then
                        if No (Annot.Spec_Capacity)
                          /= No (Current_Annot.Spec_Capacity)
                        then
                           Error_Msg_NE_If
                             ("incompatible ""Capacity"" function inherited "
                              & "from model type &",
                              Typ,
                              Model_Type,
                              Continuations =>
                                [Create
                                   ((if Present (Annot.Spec_Capacity)
                                     then "& takes the capacity as a parameter"
                                     else "& has no parameters"),
                                    Names => [Annot.Empty_Function])]);
                        end if;
                        exit;
                     end if;
                  end loop;
               end;
            end if;
      end case;

      --  Make sure that the Empty function and the Add procedure used to
      --  create the aggregate are well behaved (they do not access global data
      --  and do not have side effects).

      declare
         Globals : Global_Flow_Ids;

      begin
         Get_Globals
           (Subprogram          => Annot.Empty_Function,
            Scope               =>
              (Ent => Annot.Empty_Function, Part => Visible_Part),
            Classwide           => False,
            Globals             => Globals,
            Use_Deduced_Globals => not Gnat2Why_Args.Global_Gen_Mode,
            Ignore_Depends      => False);

         if Is_Function_With_Side_Effects (Annot.Empty_Function) then
            Error_Msg_NE_If
              ("& function shall not have side effects",
               Typ,
               Annot.Empty_Function);
         elsif not Globals.Proof_Ins.Is_Empty
           or else not Globals.Inputs.Is_Empty
         then
            Error_Msg_NE_If
              ("& function shall not access global data",
               Typ,
               Annot.Empty_Function);
         elsif Is_Volatile_Function (Annot.Empty_Function) then
            Error_Msg_NE_If
              ("& function shall not be volatile", Typ, Annot.Empty_Function);
         end if;

         Get_Globals
           (Subprogram          => Annot.Add_Procedure,
            Scope               =>
              (Ent => Annot.Add_Procedure, Part => Visible_Part),
            Classwide           => False,
            Globals             => Globals,
            Use_Deduced_Globals => not Gnat2Why_Args.Global_Gen_Mode,
            Ignore_Depends      => False);

         if not Globals.Outputs.Is_Empty then
            Error_Msg_NE_If
              ("& procedure shall not have global effects",
               Typ,
               Annot.Add_Procedure);
         elsif not Globals.Proof_Ins.Is_Empty
           or else not Globals.Inputs.Is_Empty
         then
            Error_Msg_NE_If
              ("& procedure shall not access global data",
               Typ,
               Annot.Add_Procedure);
         elsif Get_Termination_Condition (Annot.Add_Procedure)
           /= (Static, True)
         then
            Error_Msg_NE_If
              ("& procedure shall always terminate", Typ, Annot.Add_Procedure);
         elsif Has_Exceptional_Contract (Annot.Add_Procedure) then
            Error_Msg_NE_If
              ("& procedure shall not propagate exceptions",
               Typ,
               Annot.Add_Procedure);
         elsif Has_Program_Exit (Annot.Add_Procedure) then
            Error_Msg_NE_If
              ("& procedure shall not exit the program",
               Typ,
               Annot.Add_Procedure);
         end if;
      end;
   end Do_Delayed_Checks_For_Aggregates;

   ------------------------------------------
   -- Do_Delayed_Checks_On_Pragma_Annotate --
   ------------------------------------------

   procedure Do_Delayed_Checks_On_Pragma_Annotate is
   begin
      --  Go over the delayed checks for calls in contracts of subprograms
      --  with higher order specialization and do them.

      for Position in Delayed_HO_Specialization_Checks.Iterate loop
         declare
            Call : Node_Id renames Node_Maps.Key (Position);
            N    : Node_Id renames Node_Maps.Element (Position);
            Subp : constant Entity_Id := Get_Called_Entity (Call);
         begin
            pragma Assert (Entity_Marked (Subp));
            if not Has_Higher_Order_Specialization_Annotation (Subp) then
               Error_Msg_N_If
                 ("subprogram annotated with Higher_Order_Specialization"
                  & " shall only reference its access-to-function"
                  & " parameters in dereferences and as actual parameters in"
                  & " calls to functions annotated with"
                  & " Higher_Order_Specialization",
                  N);
            end if;
         end;
      end loop;
      Delayed_HO_Specialization_Checks.Clear;

      --  Go over the set of lemmas with automatic instantiation. For those
      --  associated to functions with higher order specializations, check that
      --  the lemma can be specialized and fill the mapping in
      --  Higher_Order_Spec_Annotations.

      for Lemma of Delayed_Checks_For_Lemmas loop
         declare
            Fun : Entity_Id renames
              Automatic_Instantiation_Annotations.Element (Lemma);
         begin
            if Has_Higher_Order_Specialization_Annotation (Fun) then
               Check_Automatic_Inst_And_HO_Specialization_Compatibility
                 (Lemma, Fun);
            end if;
         end;
      end loop;
      Delayed_Checks_For_Lemmas.Clear;

      --  Go over aggregate annotations to make sure that all the necessary
      --  entities have been provided.

      for Typ of Delayed_Checks_For_Aggregates loop
         Do_Delayed_Checks_For_Aggregates (Typ);
      end loop;
      Delayed_Checks_For_Aggregates.Clear;

      --  Go over hide and unhide annotations to make sure that they are
      --  compatible with the default and with the visibility of the expression
      --  function body if it is deferred to the body.

      for Position in Delayed_Hide_Compatibility_Checks.Iterate loop
         declare
            use Node_To_Node_Pairs;
            Prag  : constant Node_Id := Key (Position);
            Scope : constant Entity_Id := Element (Position).First;
            E     : constant Entity_Id := Element (Position).Snd;
            Kind  : constant Hide_Annotation_Kind :=
              Hide_Or_Unhide_Annotations (Scope) (E);
         begin
            if Potentially_Hidden_Entities (E) = Kind then
               case Kind is
                  when Hide_Expr_Fun       =>
                     Error_Msg_N_If
                       ("Hide_Info annotation is redundant, "
                        & Pretty_Source_Name (E)
                        & " is hidden by default",
                        Prag);

                  when Unhide_Expr_Fun     =>
                     Error_Msg_N_If
                       ("Unhide_Info annotation is redundant, "
                        & Pretty_Source_Name (E)
                        & " is visible by default",
                        Prag);

                  when Unhide_Package_Body =>
                     raise Program_Error;
               end case;
            end if;

            if not Gnat2Why_Args.Global_Gen_Mode
              and then Has_Refinement (E)
              and then not Has_Visibility_On_Refined (Scope, E)
            then
               Error_Msg_N_If
                 ("the body of "
                  & Pretty_Source_Name (E)
                  & " is not visible at the current location",
                  Prag);
               return;
            end if;
         end;
      end loop;
      Delayed_Hide_Compatibility_Checks.Clear;

      --  Go over null values with confirming annotations to check that the
      --  value of the constant is a null value.

      for Ent of Delayed_Null_Values loop
         pragma Assert (Is_Partial_View (Ent));
         pragma Assert (Entity_Marked (Full_View (Ent)));
         declare
            Decl : constant Node_Id := Parent (Full_View (Ent));
         begin
            if not Is_Null_Or_Reclaimed_Expr
                     (Expression (Decl), Null_Value => True)
            then
               Error_Msg_N_If
                 ("the value of "
                  & Pretty_Source_Name (Ent)
                  & " shall be a null value",
                  Decl);
               return;
            end if;
         end;
      end loop;
      Delayed_Null_Values.Clear;
   end Do_Delayed_Checks_On_Pragma_Annotate;

   ---------------------------
   -- Find_Aggregate_Aspect --
   ---------------------------

   function Find_Aggregate_Aspect (Typ : Type_Kind_Id) return Node_Id is
      Typ_With_Aspect : constant Type_Kind_Id :=
        (if Is_Scalar_Type (Typ) and then Present (First_Subtype (Typ))
         then First_Subtype (Typ)
         else Typ);
      --  If Typ is a scalar base type, it might not have the
      --  aggregate aspect. Look for it on the first subtype
      --  instead.
   begin
      return Find_Value_Of_Aspect (Typ_With_Aspect, Aspect_Aggregate);
   end Find_Aggregate_Aspect;

   ------------------------
   -- Find_Inline_Pragma --
   ------------------------

   function Find_Inline_Pragma (E : Entity_Id) return Node_Id
   is (Inline_Pragmas.Element (E));

   -----------------------------------------------
   -- Generate_Useless_Pragma_Annotate_Warnings --
   -----------------------------------------------

   procedure Generate_Useless_Pragma_Annotate_Warnings is
   begin
      --  Check whether we may issue a warning on the pragma before doing it

      for Prag of Pragma_Set loop
         if May_Issue_Warning_On_Node (Prag)
           and then not Is_In_Statically_Dead_Branch (Prag)
         then
            Warning_Msg_N_If (Warn_Pragma_Annotate_No_Check, Prag);
         end if;
      end loop;

      for Prag of Proved_Pragma loop
         if Instantiation_Location (Sloc (Prag)) = No_Location then
            Warning_Msg_N_If (Warn_Pragma_Annotate_Proved_Check, Prag);
         end if;
      end loop;
   end Generate_Useless_Pragma_Annotate_Warnings;

   ------------------------------
   -- Get_Aggregate_Annotation --
   ------------------------------

   function Get_Aggregate_Annotation
     (E : Type_Kind_Id) return Aggregate_Annotation
   is (Aggregate_Annotations.Element (Base_Retysp (E)));

   ----------------------------------------
   -- Get_Container_Function_From_Pragma --
   ----------------------------------------

   function Get_Container_Function_From_Pragma (N : Node_Id) return Entity_Id
   is
      Number_Of_Pragma_Args : constant Nat :=
        List_Length (Pragma_Argument_Associations (N));
   begin
      if Number_Of_Pragma_Args /= 4 then
         return Empty;
      end if;

      declare
         Arg2 : constant Node_Id :=
           Next (First (Pragma_Argument_Associations (N)));
         Arg4 : constant Node_Id := Next (Next (Arg2));
         Name : constant String :=
           Get_Name_String (Chars (Get_Pragma_Arg (Arg2)));
         Exp  : constant Node_Id := Expression (Arg4);

      begin
         if Name not in "container_aggregates" | "iterable_for_proof"
           or else Nkind (Exp) not in N_Has_Entity
         then
            return Empty;
         end if;

         declare
            Fun : constant Entity_Id := Entity (Exp);
         begin
            if Ekind (Fun) = E_Function then
               return Fun;
            else
               return Empty;
            end if;
         end;
      end;
   end Get_Container_Function_From_Pragma;

   --------------------------
   -- Get_Hide_Annotations --
   --------------------------

   function Get_Hide_Annotations
     (E : Entity_Id) return Node_To_Hide_Annotation_Kind_Maps.Map
   is
      use Hide_Annotations_Maps;
      Position : constant Hide_Annotations_Maps.Cursor :=
        Hide_Or_Unhide_Annotations.Find (E);
   begin
      if Has_Element (Position) then
         return Element (Position);
      else
         return Node_To_Hide_Annotation_Kind_Maps.Empty_Map;
      end if;
   end Get_Hide_Annotations;

   ------------------------------
   -- Expr_Fun_Might_Be_Hidden --
   ------------------------------

   function Expr_Fun_Might_Be_Hidden (E : Entity_Id) return Boolean
   is (Potentially_Hidden_Entities.Contains (E));
   --  For now, the expression function body is the only thing which can be
   --  hidden.

   --------------------------------
   -- Expr_Fun_Hidden_By_Default --
   --------------------------------

   function Expr_Fun_Hidden_By_Default (E : Entity_Id) return Boolean is
      use Node_To_Hide_Annotation_Kind_Maps;
      Position : constant Node_To_Hide_Annotation_Kind_Maps.Cursor :=
        Potentially_Hidden_Entities.Find (E);
   begin
      return
        Has_Element (Position) and then Element (Position) = Hide_Expr_Fun;
   end Expr_Fun_Hidden_By_Default;

   ------------------------------
   -- Get_Lemmas_To_Specialize --
   ------------------------------

   function Get_Lemmas_To_Specialize (E : Entity_Id) return Node_Sets.Set
   is (Higher_Order_Spec_Annotations.Element (E));

   --------------------
   -- Get_Null_Value --
   --------------------

   function Get_Null_Value (E : Entity_Id) return Entity_Id
   is (Predefined_Eq_Annotations (Root_Retysp (E)).Null_Value);

   ----------------------------------------
   -- Get_Ownership_Entity_From_Pragma --
   ----------------------------------------

   function Get_Ownership_Entity_From_Pragma
     (N : Node_Id; Ty : Entity_Id) return Entity_Id
   is
      Number_Of_Pragma_Args : constant Nat :=
        List_Length (Pragma_Argument_Associations (N));
   begin
      if Number_Of_Pragma_Args /= 4 then
         return Empty;
      end if;

      declare
         Arg2 : constant Node_Id :=
           Next (First (Pragma_Argument_Associations (N)));
         Arg4 : constant Node_Id := Next (Next (Arg2));
         Name : constant String :=
           Get_Name_String (Chars (Get_Pragma_Arg (Arg2)));
         Exp  : constant Node_Id := Expression (Arg4);

      begin
         if Name /= "ownership" or else Nkind (Exp) not in N_Has_Entity then
            return Empty;
         end if;

         declare
            Ent : constant Entity_Id := Entity (Exp);
         begin
            if Ekind (Ent) = E_Function
              and then Present (First_Formal (Ent))
              and then Root_Type (Etype (First_Formal (Ent))) = Root_Type (Ty)
            then
               return Ent;
            elsif Ekind (Ent) = E_Constant
              and then Root_Type (Etype (Ent)) = Root_Type (Ty)
            then
               return Ent;
            else
               return Empty;
            end if;
         end;
      end;
   end Get_Ownership_Entity_From_Pragma;

   ------------------------------------------
   -- Get_Predefined_Eq_Entity_From_Pragma --
   ------------------------------------------

   function Get_Predefined_Eq_Entity_From_Pragma
     (N : Node_Id; Ty : Entity_Id) return Entity_Id
   is
      Number_Of_Pragma_Args : constant Nat :=
        List_Length (Pragma_Argument_Associations (N));
   begin
      if Number_Of_Pragma_Args /= 4 then
         return Empty;
      end if;

      declare
         Arg2 : constant Node_Id :=
           Next (First (Pragma_Argument_Associations (N)));
         Arg4 : constant Node_Id := Next (Next (Arg2));
         Name : constant String :=
           Get_Name_String (Chars (Get_Pragma_Arg (Arg2)));
         Exp  : constant Node_Id := Expression (Arg4);

      begin
         if Name /= "predefined_equality"
           or else Nkind (Exp) not in N_Has_Entity
         then
            return Empty;
         end if;

         declare
            Ent : constant Entity_Id := Entity (Exp);
         begin
            if Ekind (Ent) = E_Constant
              and then Root_Type (Etype (Ent)) = Root_Type (Ty)
            then
               return Ent;
            else
               return Empty;
            end if;
         end;
      end;
   end Get_Predefined_Eq_Entity_From_Pragma;

   ----------------------------
   -- Get_Predefined_Eq_Kind --
   ----------------------------

   function Get_Predefined_Eq_Kind (E : Entity_Id) return Predefined_Eq_Kind
   is (Predefined_Eq_Annotations (Root_Retysp (E)).Kind);

   ------------------------------------
   -- Get_Reclamation_Check_Function --
   ------------------------------------

   function Get_Reclamation_Entity (E : Entity_Id) return Entity_Id is
      use Node_To_Ownership_Maps;
      R : constant Entity_Id := Root_Retysp (E);
   begin
      return Ownership_Annotations (R).Reclamation_Entity;
   end Get_Reclamation_Entity;

   procedure Get_Reclamation_Entity
     (E                  : Entity_Id;
      Reclamation_Entity : out Entity_Id;
      Kind               : out Reclamation_Kind;
      For_Check          : Boolean := False)
   is
      use Node_To_Ownership_Maps;
      R : constant Entity_Id :=
        (if For_Check then Retysp (E) else Root_Retysp (E));
      --  If For_Check is True, get the E's own annotation. Otherwise, get the
      --  annotation on E's root type.

   begin
      Reclamation_Entity := Ownership_Annotations (R).Reclamation_Entity;
      Kind := Ownership_Annotations (R).Reclaimed;
      pragma Assert (Ownership_Annotations (R).Confirming = For_Check);
   end Get_Reclamation_Entity;

   ------------------------------
   -- Has_Aggregate_Annotation --
   ------------------------------

   function Has_Aggregate_Annotation (E : Type_Kind_Id) return Boolean
   is (Aggregate_Annotations.Contains (Base_Retysp (E)));

   ----------------------------------
   -- Has_At_End_Borrow_Annotation --
   ----------------------------------

   function Has_At_End_Borrow_Annotation (E : Entity_Id) return Boolean
   is (Ekind (E) = E_Function and then At_End_Borrow_Annotations.Contains (E));

   --------------------------------------------
   -- Has_Automatic_Instantiation_Annotation --
   --------------------------------------------

   function Has_Automatic_Instantiation_Annotation
     (E : Entity_Id) return Boolean
   is (Automatic_Instantiation_Annotations.Contains (E));

   ----------------------------
   -- Has_Handler_Annotation --
   ----------------------------

   function Has_Handler_Annotation (E : Type_Kind_Id) return Boolean
   is (Handler_Annotations.Contains (Base_Retysp (E)));

   -----------------------------
   -- Has_Hidden_Private_Part --
   -----------------------------

   function Has_Hidden_Private_Part (E : Entity_Id) return Boolean is
      use Node_To_Bool_Maps;
      Pos : Node_To_Bool_Maps.Cursor :=
        Potentially_Hidden_Private_Parts.Find (E);
   begin
      --  If there is no association for E in Potentially_Hidden_Private_Parts,
      --  look at pragma Annotate at the beginning of E's private part.

      if not Has_Element (Pos) then
         declare
            Spec : constant Node_Id := Package_Specification (E);
            Cur  : Node_Id := First (Private_Declarations (Spec));

         begin
            --  Handle GNATprove annotations at the beginning of the package
            --  private part.

            while Present (Cur) loop
               if Is_Pragma_Annotate_GNATprove (Cur) then
                  if List_Length (Pragma_Argument_Associations (Cur)) = 3 then
                     declare
                        Arg2 : constant Node_Id :=
                          Next (First (Pragma_Argument_Associations (Cur)));
                        Arg3 : constant Node_Id := Next (Arg2);
                        Name : constant String :=
                          Get_Name_String (Chars (Get_Pragma_Arg (Arg2)));
                        Exp  : constant Node_Id := Expression (Arg3);

                     begin
                        if Name = "hide_info"
                          and then Nkind (Exp) in N_String_Literal
                          and then
                            To_Lower (To_String (Strval (Exp)))
                            = "private_part"
                        then
                           Mark_Pragma_Annotate
                             (Cur, Spec, Consider_Next => True);
                        end if;
                     end;
                  end if;
               elsif Decl_Starts_Pragma_Annotate_Range (Cur)
                 and then Nkind (Cur) not in N_Pragma | N_Null_Statement
               then
                  exit;
               end if;
               Next (Cur);
            end loop;
         end;

         --  If we have found an applicable pragma, the map will have been
         --  updated. Otherwise, update the map to register that there are no
         --  such pragmas.

         declare
            Inserted : Boolean;
         begin
            Potentially_Hidden_Private_Parts.Insert (E, False, Pos, Inserted);
         end;
      end if;

      return Element (Pos);
   end Has_Hidden_Private_Part;

   ------------------------------------------------
   -- Has_Higher_Order_Specialization_Annotation --
   ------------------------------------------------

   function Has_Higher_Order_Specialization_Annotation
     (E : Entity_Id) return Boolean
   is (Higher_Order_Spec_Annotations.Contains (E));

   -------------------------------
   -- Has_Logical_Eq_Annotation --
   -------------------------------

   function Has_Logical_Eq_Annotation (E : Entity_Id) return Boolean
   is (Ekind (E) = E_Function and then Logical_Eq_Annotations.Contains (E));

   ------------------------------------------
   -- Has_No_Bitwise_Operations_Annotation --
   ------------------------------------------

   function Has_No_Bitwise_Operations_Annotation (E : Entity_Id) return Boolean
   is (No_Bitwise_Operations_Annotations.Contains (E));

   -----------------------------------
   -- Has_No_Wrap_Around_Annotation --
   -----------------------------------

   function Has_No_Wrap_Around_Annotation (E : Entity_Id) return Boolean
   is (No_Wrap_Around_Annotations.Contains (E));

   -------------------------------------
   -- Has_Mutable_In_Param_Annotation --
   -------------------------------------

   function Has_Mutable_In_Param_Annotation (E : Entity_Id) return Boolean is
      Position : constant Common_Containers.Node_Graphs.Cursor :=
        Mutable_In_Params_Annotations.Find (Scope (E));
   begin
      return
        Common_Containers.Node_Graphs.Has_Element (Position)
        and then
          Mutable_In_Params_Annotations (Position).Contains
            (Retysp (Etype (E)));
   end Has_Mutable_In_Param_Annotation;

   ----------------------------------
   -- Has_Own_Ownership_Annotation --
   ----------------------------------

   function Has_Own_Ownership_Annotation (E : Entity_Id) return Boolean
   is (Ownership_Annotations.Contains (Retysp (E)));

   ------------------------------
   -- Has_Ownership_Annotation --
   ------------------------------

   function Has_Ownership_Annotation (E : Entity_Id) return Boolean is
      use Node_To_Ownership_Maps;
      Position : constant Node_To_Ownership_Maps.Cursor :=
        Ownership_Annotations.Find (Root_Retysp (E));
   begin
      return
        Has_Element (Position)
        and then not Ownership_Annotations (Position).Confirming;
   end Has_Ownership_Annotation;

   --------------------------------------
   -- Has_Own_Predefined_Eq_Annotation --
   --------------------------------------

   function Has_Own_Predefined_Eq_Annotation (E : Entity_Id) return Boolean
   is (Predefined_Eq_Annotations.Contains (Retysp (E)));

   ----------------------------------
   -- Has_Predefined_Eq_Annotation --
   ----------------------------------

   function Has_Predefined_Eq_Annotation (E : Entity_Id) return Boolean is
      use Node_To_Predefined_Eq_Maps;
      Rep_Ty : constant Entity_Id :=
        (if Is_Tagged_Type (Retysp (E))
         then Base_Retysp (E)
         else Root_Retysp (E));
      --  On tagged types, the predefined equality annotation is not inherited.
      --  The primitive equality function can be used to override the handling
      --  on the inherited part.

      Position : constant Node_To_Predefined_Eq_Maps.Cursor :=
        Predefined_Eq_Annotations.Find (Rep_Ty);
   begin
      return
        Has_Element (Position)
        and then not Predefined_Eq_Annotations (Position).Confirming;
   end Has_Predefined_Eq_Annotation;

   ----------------------------------------
   -- Has_Skip_Flow_And_Proof_Annotation --
   ----------------------------------------

   function Has_Skip_Flow_And_Proof_Annotation (E : Entity_Id) return Boolean
   is
      Cur : Entity_Id := E;
   begin
      loop
         if Skip_Flow_And_Proof_Annotations.Contains (Cur) then
            return True;
         end if;
         Cur := Scope (Cur);
         exit when No (Cur);
      end loop;
      return False;
   end Has_Skip_Flow_And_Proof_Annotation;

   -------------------------------
   -- Has_Skip_Proof_Annotation --
   -------------------------------

   function Has_Skip_Proof_Annotation (E : Entity_Id) return Boolean is
      Cur : Entity_Id := E;
   begin
      loop
         if Skip_Proof_Annotations.Contains (Cur)
           or else Skip_Flow_And_Proof_Annotations.Contains (Cur)
         then
            return True;
         end if;
         Cur := Scope (Cur);
         exit when No (Cur);
      end loop;
      return False;
   end Has_Skip_Proof_Annotation;

   ------------------------------
   -- Has_Visible_Package_Body --
   ------------------------------

   function Has_Visible_Package_Body (E : Entity_Id) return Boolean is
      use Node_To_Hide_Annotation_Kind_Maps;
      Position : constant Node_To_Hide_Annotation_Kind_Maps.Cursor :=
        Potentially_Hidden_Entities.Find (E);
   begin
      pragma
        Assert
          (if Has_Element (Position)
           then Element (Position) = Unhide_Package_Body);
      return Has_Element (Position);
   end Has_Visible_Package_Body;

   ------------------------------------------------
   -- Is_Pragma_Annotate_Automatic_Instantiation --
   ------------------------------------------------

   function Is_Pragma_Annotate_Automatic_Instantiation
     (N : Node_Id; P : Entity_Id := Empty) return Boolean
   is
      Number_Of_Pragma_Args : constant Nat :=
        List_Length (Pragma_Argument_Associations (N));
      Arg1                  : constant Node_Id :=
        First (Pragma_Argument_Associations (N));
      Arg2                  : constant Node_Id := Next (Arg1);
      Name                  : constant String :=
        (if No (Arg2)
         then ""
         else Get_Name_String (Chars (Get_Pragma_Arg (Arg2))));
      Arg3                  : Node_Id;
      Arg3_Exp              : Node_Id := Empty;

   begin
      if Name /= "automatic_instantiation" or else Number_Of_Pragma_Args /= 3
      then
         return False;
      end if;

      Arg3 := Next (Arg2);
      Arg3_Exp := Expression (Arg3);
      return
        Nkind (Arg3_Exp) in N_Has_Entity
        and then (No (P) or else Entity (Arg3_Exp) = P);
   end Is_Pragma_Annotate_Automatic_Instantiation;

   -----------------------------
   -- Infer_Inline_Annotation --
   -----------------------------

   procedure Infer_Inline_Annotation (E : E_Function_Id) is
      Nodes : Common_Containers.Node_Lists.List;
      Value : Node_Id;

   begin
      --  Check that E does not have a postcondition

      Nodes := Find_Contracts (E, Pragma_Postcondition, False, False);

      if not Nodes.Is_Empty then
         return;

      --  Check that E is an expression function

      elsif not Is_Expression_Function_Or_Completion (E) then
         return;

      --  ...whose body is in SPARK

      elsif not SPARK_Definition.Entity_Body_Compatible_With_SPARK (E) then
         return;

      --  ...it is not a traversal function

      elsif Is_Traversal_Function (E) then
         return;

      --  ...and it cannot be specialized

      elsif Has_Higher_Order_Specialization_Annotation (E) then
         return;

      else
         Value := Expression (Get_Expression_Function (E));

         if Contains_Function_Call (Value) then
            return;
         else
            Inferred_Inline_Annotations.Include (E, Value);
         end if;
      end if;
   end Infer_Inline_Annotation;

   --------------------------------
   -- Infer_Ownership_Annotation --
   --------------------------------

   procedure Infer_Ownership_Annotation (E : Type_Kind_Id) is
      pragma Assert (E = Root_Retysp (E));
   begin
      if Is_Deep (E) and then not Ownership_Annotations.Contains (E) then
         if Contains_Allocated_Parts (E) then
            Ownership_Annotations.Insert
              (Key      => E,
               New_Item =>
                 Ownership_Annotation'
                   (Needs_Reclamation => True,
                    Confirming        => False,
                    others            => <>));
         else
            Ownership_Annotations.Insert
              (Key      => E,
               New_Item =>
                 Ownership_Annotation'
                   (Needs_Reclamation => False, Confirming => False));
         end if;
      end if;
   end Infer_Ownership_Annotation;

   ---------------------------
   -- Insert_Annotate_Range --
   ---------------------------

   procedure Insert_Annotate_Range
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      Range_Node      : Node_Id;
      Whole           : Boolean)
   is
      Left_Sloc, Right_Sloc : Source_Ptr;
   begin
      if No (Range_Node) then
         return;
      end if;

      --  In the case of a pragma on the body, we also need to include the spec
      --  node.

      if Nkind (Range_Node) = N_Subprogram_Body
        and then Present (Corresponding_Spec (Range_Node))
      then
         Insert_Annotate_Range
           (Prgma,
            Kind,
            Pattern,
            Reason,
            Specification (Range_Node),
            Whole => True);
         Sloc_Range (Range_Node, Left_Sloc, Right_Sloc);
         Insert_Annotate_Range
           (Prgma, Kind, Pattern, Reason, Left_Sloc, Right_Sloc);
         declare
            Spec_Node : constant Node_Id :=
              Parent (Parent (Corresponding_Spec (Range_Node)));
         begin

            --  The spec might be just before the body, so Insert_With_Next
            --  might loop indefinitely. We use the Exclude argument to skip
            --  our own current node in that case, to prevent an infinite loop.

            Insert_With_Next
              (Prgma, Kind, Pattern, Reason, Spec_Node, Skip => Range_Node);
         end;
         return;
      end if;
      if Whole then
         Sloc_Range (Range_Node, Left_Sloc, Right_Sloc);

         --  Sloc_Range doesn't take into account aspect specifications
         --  attached to the node, so we do this ourselves here.

         if Permits_Aspect_Specifications (Range_Node) then
            declare
               N : Node_Id := First (Aspect_Specifications (Range_Node));
            begin
               while Present (N) loop
                  Insert_Annotate_Range
                    (Prgma, Kind, Pattern, Reason, N, Whole);
                  Next (N);
               end loop;
            end;
         end if;
      else
         Left_Sloc := Errout.First_Sloc (Range_Node);
         Right_Sloc := Errout.First_Sloc (Prgma);
      end if;
      Insert_Annotate_Range
        (Prgma, Kind, Pattern, Reason, Left_Sloc, Right_Sloc);
   end Insert_Annotate_Range;

   procedure Insert_Annotate_Range
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      First, Last     : Source_Ptr)
   is
      use Annot_Ranges;

      Cur : Annot_Ranges.Cursor := Annotations.First;
   begin
      Pragma_Set.Include (Prgma);
      while Has_Element (Cur) and then First > Annotations (Cur).First loop
         Next (Cur);
      end loop;
      Annotations.Insert
        (Before   => Cur,
         New_Item =>
           (Present => True,
            Kind    => Kind,
            First   => First,
            Last    => Last,
            Pattern => Pattern,
            Reason  => Reason,
            Prgma   => Prgma));

      pragma Assert (Annot_Range_Sorting.Is_Sorted (Annotations));
   end Insert_Annotate_Range;

   ----------------------
   -- Insert_With_Next --
   ----------------------

   procedure Insert_With_Next
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      First_Node      : Node_Id;
      Skip            : Node_Id := Empty)
   is
      Node : Node_Id := First_Node;
   begin
      Insert_Annotate_Range
        (Prgma, Kind, Pattern, Reason, Node, Whole => True);
      Next (Node);
      while Present (Node)
        and then not Comes_From_Source (Node)
        and then Nkind (Node) /= N_Expression_Function
      loop
         if Node /= Skip then
            Insert_Annotate_Range
              (Prgma, Kind, Pattern, Reason, Node, Whole => True);
         end if;
         Next (Node);
      end loop;
   end Insert_With_Next;

   --------------------------
   -- Mark_Pragma_Annotate --
   --------------------------

   procedure Mark_Pragma_Annotate
     (N : Node_Id; Preceding : Node_Id; Consider_Next : Boolean)
   is
      Result : Check_Justification;
   begin
      if Pragma_Seen.Contains (N) then
         return;
      else
         Pragma_Seen.Insert (N);
      end if;

      Check_Pragma_Annotate_GNATprove (N, Result);

      case Result.Present is
         when False =>
            return;

         when True  =>
            if Consider_Next then
               Insert_With_Next
                 (N, Result.Kind, Result.Pattern, Result.Reason, Preceding);
            else
               Insert_Annotate_Range
                 (N,
                  Result.Kind,
                  Result.Pattern,
                  Result.Reason,
                  Preceding,
                  Whole => False);
            end if;
      end case;
   end Mark_Pragma_Annotate;

   ---------------------------
   -- Needs_Ownership_Check --
   ---------------------------

   function Needs_Ownership_Check (E : Entity_Id) return Boolean is
      use Node_To_Ownership_Maps;
      Position : constant Node_To_Ownership_Maps.Cursor :=
        Ownership_Annotations.Find (Retysp (E));
   begin
      return
        Has_Element (Position)
        and then Ownership_Annotations (Position).Confirming
        and then Ownership_Annotations (Position).Needs_Reclamation
        and then Present (Ownership_Annotations (Position).Reclamation_Entity);
   end Needs_Ownership_Check;

   -----------------------
   -- Needs_Reclamation --
   -----------------------

   function Needs_Reclamation (E : Entity_Id) return Boolean
   is (Ownership_Annotations (Root_Retysp (E)).Needs_Reclamation);

   ---------------------------------------
   -- Pull_Entities_For_Annotate_Pragma --
   ---------------------------------------

   procedure Pull_Entities_For_Annotate_Pragma
     (E                 : Entity_Id;
      Queue_For_Marking : not null access procedure (E : Entity_Id)) is
   begin
      --  If E is a private type with ownership which needs reclamation, go
      --  over the following declarations to try and find its reclamation
      --  function. Do not use the getter functions as they discard confirming
      --  annotations.

      if Is_Type (E)
        and then Is_Partial_View (E)
        and then Ownership_Annotations.Contains (Retysp (E))
        and then Ownership_Annotations (Retysp (E)).Needs_Reclamation
        and then No (Ownership_Annotations (Retysp (E)).Reclamation_Entity)
      then
         declare
            Decl_Node : constant Node_Id := Declaration_Node (E);
            Cur       : Node_Id;
            Ent       : Entity_Id := Empty;
         begin
            if Is_List_Member (Decl_Node) then
               Cur := Next (Decl_Node);
               while Present (Cur) loop
                  if Is_Pragma_Annotate_GNATprove (Cur) then
                     Ent := Get_Ownership_Entity_From_Pragma (Cur, E);
                     if Present (Ent) then
                        Queue_For_Marking (Ent);
                        exit;
                     end if;
                  end if;
                  Next (Cur);
               end loop;
            end if;

            if No (Ent) and then Emit_Warning_Info_Messages then
               Warning_Msg_N
                 (Warn_No_Reclam_Func,
                  E,
                  Continuations =>
                    [Create
                       ("checks for ressource or memory reclamation will be"
                        & " unprovable")]);
            end if;
         end;
      end if;

      --  If E is a private type with predefined equality of kind "Only_Null",
      --  go over the following declarations to try and find its null value.
      --  Do not use the getter functions as they discard confirming
      --  annotations.

      if Is_Type (E)
        and then Is_Partial_View (E)
        and then Predefined_Eq_Annotations.Contains (Retysp (E))
        and then Predefined_Eq_Annotations (Retysp (E)).Kind = Only_Null
        and then No (Predefined_Eq_Annotations (Retysp (E)).Null_Value)
      then
         declare
            Decl_Node : constant Node_Id := Declaration_Node (E);
            Cur       : Node_Id;
            Ent       : Entity_Id := Empty;
         begin
            if Is_List_Member (Decl_Node) then
               Cur := Next (Decl_Node);
               while Present (Cur) loop
                  if Is_Pragma_Annotate_GNATprove (Cur) then
                     Ent := Get_Predefined_Eq_Entity_From_Pragma (Cur, E);
                     if Present (Ent) then
                        Queue_For_Marking (Ent);
                        exit;
                     end if;
                  end if;
                  Next (Cur);
               end loop;
            end if;

            if No (Ent) and then Emit_Warning_Info_Messages then
               Warning_Msg_N
                 (Warn_Predef_Eq_Null,
                  E,
                  Continuations =>
                    [Create
                       ("consider annotating a constant with a pragma "
                        & "Annotate "
                        & "(GNATprove, Predefined_Equality, ""Null_Value"""
                        & ", ...)")]);
            end if;
         end;
      end if;

      --  If E is annotated with Container_Aggregates or has an Iterable
      --  aspect, go over the following declarations to try and find its
      --  associated functions.

      if Is_Type (E)
        and then Is_Base_Type (E)
        and then
          (Has_Aggregate_Annotation (E)
           or else Has_Iterable_Aspect_In_SPARK (E))
      then
         declare
            Decl_Node : constant Node_Id := Declaration_Node (E);
            Cur       : Node_Id;
         begin
            if Is_List_Member (Decl_Node) then
               Cur := First (List_Containing (Decl_Node));
               while Present (Cur) loop
                  if Is_Pragma_Annotate_GNATprove (Cur) then
                     declare
                        Fun : constant Entity_Id :=
                          Get_Container_Function_From_Pragma (Cur);
                     begin
                        if Present (Fun) then
                           Queue_For_Marking (Fun);
                        end if;
                     end;
                  end if;
                  Next (Cur);
               end loop;
            end if;
         end;
      end if;

      --  If E is a lemma procedure annotated with Automatic_Instantiation,
      --  also mark its associated function.

      if Has_Automatic_Instantiation_Annotation (E) then
         Queue_For_Marking (Retrieve_Automatic_Instantiation_Annotation (E));

      --  Go over the ghost procedure declaration directly following E to
      --  mark them in case they are lemmas with automatic instantiation.
      --  We assume that lemma procedures associated to E are declared just
      --  after E, possibly interspaced with compiler generated stuff and
      --  pragmas and that the pragma Automatic_Instantiation is always
      --  located directly after the lemma procedure declaration.

      elsif Ekind (E) = E_Function
        and then not Is_Volatile_Function (E)
        and then not Is_Function_With_Side_Effects (E)
      then
         declare
            Decl_Node : constant Node_Id := Parent (Declaration_Node (E));
            Cur       : Node_Id;
            Proc      : Entity_Id := Empty;

         begin
            if Is_List_Member (Decl_Node)
              and then Decl_Starts_Pragma_Annotate_Range (Decl_Node)
            then
               Cur := Next (Decl_Node);
               while Present (Cur) loop

                  --  We have found a pragma Automatic_Instantiation that
                  --  applies to Proc, add Proc to the queue for marking and
                  --  continue the search.

                  if Present (Proc)
                    and then Is_Pragma_Annotate_GNATprove (Cur)
                    and then
                      Is_Pragma_Annotate_Automatic_Instantiation (Cur, Proc)
                  then
                     Queue_For_Marking (Proc);
                     Proc := Empty;

                  --  Ignore other pragmas

                  elsif Nkind (Cur) = N_Pragma then
                     null;

                  --  We have found a declaration. If Cur is not a lemma
                  --  procedure annotated with Automatic_Instantiation we
                  --  can stop the search.

                  elsif Decl_Starts_Pragma_Annotate_Range (Cur) then

                     --  Cur is a declaration of a ghost procedure. Store
                     --  it in Proc and continue the search to see if there
                     --  is an associated Automatic_Instantiation
                     --  Annotation. If there is already something in Proc,
                     --  stop the search as no pragma
                     --  Automatic_Instantiation has been found directly
                     --  after the declaration of Proc.

                     if Nkind (Cur) = N_Subprogram_Declaration
                       and then
                         Ekind (Unique_Defining_Entity (Cur)) = E_Procedure
                       and then Is_Ghost_Entity (Unique_Defining_Entity (Cur))
                       and then No (Proc)
                     then
                        Proc := Unique_Defining_Entity (Cur);

                     --  We have found a declaration which is not a lemma
                     --  procedure, we can stop the search.

                     else
                        exit;
                     end if;
                  end if;
                  Next (Cur);
               end loop;
            end if;
         end;
      end if;
   end Pull_Entities_For_Annotate_Pragma;

   -------------------------------------------------
   -- Retrieve_Automatic_Instantiation_Annotation --
   -------------------------------------------------

   function Retrieve_Automatic_Instantiation_Annotation
     (E : Entity_Id) return Entity_Id
   is (Automatic_Instantiation_Annotations.Element (E));

   --------------------------------
   -- Retrieve_Inline_Annotation --
   --------------------------------

   function Retrieve_Inline_Annotation (E : Entity_Id) return Node_Id is

      function Refinement_Is_Always_Visible
        (Subp : Callable_Kind_Id) return Boolean
      with Pre => Has_Refinement (Subp);
      --  Return True if the Refined_Post or deferred body of Subp is always
      --  visible from the compilation unit.

      ----------------------------------
      -- Refinement_Is_Always_Visible --
      ----------------------------------

      function Refinement_Is_Always_Visible
        (Subp : Callable_Kind_Id) return Boolean
      is
         Subp_Scop : Entity_Id := Enclosing_Unit (Subp);
      begin
         pragma Assert (Present (Subp_Scop));

         --  For visible package bodies, go to the enclosing unit, as it has
         --  visibility.

         while Ekind (Subp_Scop) = E_Package
           and then Has_Visible_Package_Body (Subp_Scop)
         loop
            Subp_Scop := Enclosing_Unit (Subp_Scop);
         end loop;

         --  If Subp_Scop is not a nested package or protected type, or if it
         --  is the analyzed unit, then the refinement of Subp is always
         --  visible.

         return
           Ekind (Subp_Scop) not in E_Package | E_Protected_Type
           or else
             (Is_Compilation_Unit (Subp_Scop)
              and then Is_In_Analyzed_Files (Subp_Scop));
      end Refinement_Is_Always_Visible;

      Position : Common_Containers.Node_Maps.Cursor :=
        Inline_Annotations.Find (E);

   begin
      --  Do not infer inline annotations for potentially hidden functions nor
      --  for deferred expression functions from nested packages.

      if not Common_Containers.Node_Maps.Has_Element (Position)
        and then not Potentially_Hidden_Entities.Contains (E)
        and then
          (not Has_Refinement (E) or else Refinement_Is_Always_Visible (E))
      then
         Position := Inferred_Inline_Annotations.Find (E);
      end if;
      if not Common_Containers.Node_Maps.Has_Element (Position) then
         return Empty;
      else
         return Common_Containers.Node_Maps.Element (Position);
      end if;
   end Retrieve_Inline_Annotation;

   ----------------------------------
   -- Retrieve_Iterable_Annotation --
   ----------------------------------

   procedure Retrieve_Iterable_Annotation
     (Container_Type : Entity_Id;
      Found          : out Boolean;
      Info           : out Iterable_Annotation)
   is
      Iterable_Node : constant Node_Id :=
        Find_Value_Of_Aspect (Container_Type, Aspect_Iterable);
      C             : constant Iterable_Maps.Cursor :=
        Iterable_Annotations.Find (Iterable_Node);
   begin
      Found := Iterable_Maps.Has_Element (C);
      if Found then
         Info := Iterable_Annotations (C);
      end if;
   end Retrieve_Iterable_Annotation;

   ---------------------------------------
   -- Retrieve_Parameter_Specialization --
   ---------------------------------------

   function Retrieve_Parameter_Specialization
     (E : Entity_Id) return Node_Maps.Map
   is (Higher_Order_Lemma_Specializations (E));

   -------------------------------------
   -- Check_Pragma_Annotate_GNATprove --
   -------------------------------------

   procedure Check_Pragma_Annotate_GNATprove
     (Prag : Node_Id; Result : out Check_Justification)
   is
      --  Local constants

      From_Aspect           : constant Boolean :=
        From_Aspect_Specification (Prag);
      Aspect_Or_Pragma      : constant String :=
        (if From_Aspect then "aspect" else "pragma");
      Number_Of_Pragma_Args : constant Nat :=
        List_Length (Pragma_Argument_Associations (Prag));

      --  Local subprograms

      procedure Check_Argument_Number
        (Name : String; Num : Pos; Ok : out Boolean);
      --  Check that annotation for Name has Num arguments. Set Ok to True in
      --  that case, to False otherwise.

      function Get_Annotation_Name (Arg : Node_Id) return String;
      --  Return the name for the Annotate pragma/aspect

      ---------------------------
      -- Check_Argument_Number --
      ---------------------------

      procedure Check_Argument_Number
        (Name : String; Num : Pos; Ok : out Boolean) is
      begin
         Ok := (Num = Number_Of_Pragma_Args);

         if not Ok then
            Mark_Incorrect_Use_Of_Annotation
              (Annot_Argument_Number,
               Prag,
               Name        => Standard_Ada_Case (Name),
               From_Aspect => From_Aspect,
               Cont_Msg    => Create ("expected" & Num'Image & " arguments"));
         end if;
      end Check_Argument_Number;

      -------------------------
      -- Get_Annotation_Name --
      -------------------------

      function Get_Annotation_Name (Arg : Node_Id) return String is
      begin
         if No (Arg) then
            Error_Msg_N_If
              ("missing name in Annotate "
               & Aspect_Or_Pragma
               & " for GNATprove",
               Prag);
            return "";
         else
            pragma Assert (Nkind (Get_Pragma_Arg (Arg)) = N_Identifier);
            return Get_Name_String (Chars (Get_Pragma_Arg (Arg)));
         end if;
      end Get_Annotation_Name;

      --  Local variables

      Arg1 : constant Node_Id := First (Pragma_Argument_Associations (Prag));
      Arg2 : constant Node_Id := Next (Arg1);
      Name : constant String := Get_Annotation_Name (Arg2);

      Arg3, Arg4         : Node_Id;
      Arg3_Exp, Arg4_Exp : Node_Id := Empty;
      Ok                 : Boolean;

   begin
      --  Error case for which a message is issued in Get_Annotation_Name

      if Name = "" then
         return;
      end if;

      --  Retrieve all arguments

      if Number_Of_Pragma_Args >= 3 then
         Arg3 := Next (Arg2);
         Arg3_Exp := Expression (Arg3);
      end if;

      if Number_Of_Pragma_Args >= 4 then
         Arg4 := Next (Arg3);
         Arg4_Exp := Expression (Arg4);
      end if;

      --  Check the name and number of arguments

      if Name = "external_axiomatization" then
         Warning_Msg_N_If (Warn_Pragma_External_Axiomatization, Prag);
         return;

      elsif Name in "always_return" | "terminating" | "might_not_return" then
         declare
            Conts : Message_Lists.List;
         begin
            if Present (Arg3_Exp)
              and then Nkind (Arg3_Exp) in N_Has_Entity
              and then Ekind (Entity (Arg3_Exp)) = E_Function
            then
               Conts.Append
                 (Create ("terminating annotation is implicit on functions"));
            else
               declare
                  Deprecated : constant String :=
                    (if From_Aspect
                     then """with Annotate => (GNATprove, " & Name & ")"""
                     else
                       """pragma Annotate (GNATprove, " & Name & ", ...)""");
                  New_Syntax : constant String :=
                    (if Name in "always_return" | "terminating"
                     then """with Always_Terminates"""
                     else
                       """with Always_Terminates => False"" or use an"
                       & " exceptional contract or program exit postcondition")
                    & (if not From_Aspect
                       then " on the corresponding entity"
                       else "");
               begin
                  Conts.Append
                    (Create ("replace " & Deprecated & " by " & New_Syntax));
               end;
            end if;
            Warning_Msg_N_If
              (Warn_Pragma_Annotate_Terminating, Prag, Continuations => Conts);
         end;
         return;

      elsif Name = "at_end_borrow"
        or else Name = "automatic_instantiation"
        or else Name = "handler"
        or else Name = "higher_order_specialization"
        or else Name = "init_by_proof"
        or else Name = "inline_for_proof"
        or else Name = "logical_equal"
        or else Name = "mutable_in_parameters"
        or else Name = "no_bitwise_operations"
        or else Name = "no_wrap_around"
        or else Name = "skip_proof"
        or else Name = "skip_flow_and_proof"
      then
         Check_Argument_Number (Name, 3, Ok);

      elsif Name = "iterable_for_proof"
        or else Name = "container_aggregates"
        or else Name = "predefined_equality"
        or else
          (not From_Aspect
           and then (Name = "false_positive" or else Name = "intentional"))
      then
         Check_Argument_Number (Name, 4, Ok);

      --  Ownership and Hide_Info/Unhide_Info annotations can have 3 or 4
      --  arguments.

      elsif Name = "ownership"
        or else Name = "hide_info"
        or else Name = "unhide_info"
      then
         if Number_Of_Pragma_Args <= 3 then
            Check_Argument_Number (Name, 3, Ok);
         else
            Check_Argument_Number (Name, 4, Ok);
         end if;

      --  Annotations for justifying check messages may be attached to an
      --  entity through an aspect notation, in which case a fifth generated
      --  argument denotes the entity to which the aspect applies.

      elsif From_Aspect
        and then (Name = "false_positive" or else Name = "intentional")
      then
         Check_Argument_Number (Name, 5, Ok);

      else
         Mark_Incorrect_Use_Of_Annotation
           (Annot_Invalid_Name,
            Arg2,
            From_Aspect => From_Aspect,
            Name        => Standard_Ada_Case (Name));
         Ok := False;
      end if;

      if not Ok then
         return;
      end if;

      --  Annotations that do not correspond to justifying a check message
      --  result in Result.Present being set to False after verifying the
      --  syntax and semantics of the pragma/aspect.

      --  Annotations with 3 arguments

      if Name = "at_end_borrow" then
         Check_At_End_Borrow_Annotation (Arg3_Exp, Prag);

      elsif Name = "automatic_instantiation" then
         Check_Automatic_Instantiation_Annotation (Arg3_Exp, Prag);

      elsif Name = "container_aggregates" then
         Check_Aggregate_Annotation (Arg3_Exp, Arg4_Exp, Prag);

      elsif Name = "inline_for_proof" then
         Check_Inline_Annotation (Arg3_Exp, Prag);

      elsif Name = "handler" then
         Check_Handler_Annotation (Arg3_Exp, Prag);

      elsif Name = "hide_info" then
         Check_Hide_Annotation
           (Aspect_Or_Pragma, Arg3_Exp, Arg4_Exp, False, Prag);

      elsif Name = "unhide_info" then
         Check_Hide_Annotation
           (Aspect_Or_Pragma, Arg3_Exp, Arg4_Exp, True, Prag);

      elsif Name = "higher_order_specialization" then
         Check_Higher_Order_Specialization_Annotation (Arg3_Exp, Prag);

      elsif Name = "logical_equal" then
         Check_Logical_Equal_Annotation (Arg3_Exp, Prag);

      elsif Name = "mutable_in_parameters" then
         Check_Mutable_In_Parameters_Annotation (Arg3_Exp, Prag);

      elsif Name = "no_bitwise_operations" then
         Check_No_Bitwise_Operations_Annotation (Arg3_Exp, Prag);

      elsif Name = "no_wrap_around" then
         Check_No_Wrap_Around_Annotation (Arg3_Exp, Prag);

      --  Annotations with 4 arguments

      elsif Name = "ownership" then
         Check_Ownership_Annotation
           (Aspect_Or_Pragma, Arg3_Exp, Arg4_Exp, Prag);

      elsif Name = "iterable_for_proof" then
         Check_Iterable_Annotation (Arg3_Exp, Arg4_Exp, Prag);

      elsif Name = "skip_proof" or else Name = "skip_flow_and_proof" then
         Check_Skip_Annotations (Name, Arg3_Exp, Prag);

      elsif Name = "predefined_equality" then
         Check_Predefined_Eq_Annotation
           (Aspect_Or_Pragma, Arg3_Exp, Arg4_Exp, Prag);

      --  Annotation for justifying check messages. This is where we set
      --  Result.Present to True and fill in values for components Kind,
      --  Pattern and Reason.

      else
         declare
            Pattern, Reason : String_Id;
            Kind            : Annotate_Kind;

         begin
            if Name = "false_positive" then
               Kind := False_Positive;
            elsif Name = "intentional" then
               Kind := Intentional;
            else
               raise Program_Error;
            end if;

            --  We check for operator symbols as well as string literals,
            --  as things such as "*" are parsed as the operator symbol
            --  "multiply".

            if Nkind (Arg3_Exp) in N_String_Literal | N_Operator_Symbol then
               Pattern := Strval (Arg3_Exp);
            else
               Error_Msg_N_If
                 ("third argument ""Pattern"" for GNATprove Annotate "
                  & Aspect_Or_Pragma
                  & " must be a string literal",
                  Prag);
               return;
            end if;

            if Nkind (Arg4_Exp) = N_String_Literal then
               Reason := Strval (Arg4_Exp);
            else
               Error_Msg_N_If
                 ("fourth argument ""Reason"" for GNATprove Annotate "
                  & Aspect_Or_Pragma
                  & " must be a string literal",
                  Prag);
               return;
            end if;

            Result :=
              Check_Justification'
                (Present => True,
                 Kind    => Kind,
                 Pattern => Pattern,
                 Reason  => Reason);
         end;
      end if;
   end Check_Pragma_Annotate_GNATprove;

   ---------------------------------
   -- Check_Skip_Proof_Annotation --
   ---------------------------------

   procedure Check_Skip_Annotations
     (Name : String; Arg3_Exp : Node_Id; Prag : Node_Id)
   is
      From_Aspect      : constant Boolean := From_Aspect_Specification (Prag);
      Aspect_Or_Pragma : constant String :=
        (if From_Aspect then "aspect" else "pragma");
      E                : Entity_Id;
      Ok               : Boolean;
      Error_Msg_Name   : constant String :=
        (if Name = "skip_proof" then "Skip_Proof" else "Skip_Flow_And_Proof");
   begin
      Check_Annotate_Entity_Argument (Arg3_Exp, Prag, Error_Msg_Name, Ok);

      if not Ok then
         return;
      end if;

      E := Unique_Entity (Entity (Arg3_Exp));

      --  This entity must be a unit of analysis

      if Ekind (E)
         not in Subprogram_Kind
              | Generic_Subprogram_Kind
              | E_Task_Type
              | Entry_Kind
              | E_Package
              | E_Generic_Package
      then
         Error_Msg_N_If
           (Aspect_Or_Pragma
            & " Annotate Skip_Proof must apply to a"
            & " subprogram, task, entry or package",
            Arg3_Exp);
         return;
      end if;

      Check_Annotate_Placement (E, Prag, Error_Msg_Name, Ok);

      if not Ok then
         return;
      end if;

      --  If we already are in the scope of a Skip_Flow_And_Proof pragma, it's
      --  not allowed to use the Skip_Proof variant. Check for this case.

      if Name = "skip_proof" and then Has_Skip_Flow_And_Proof_Annotation (E)
      then
         Error_Msg_N_If
           (Aspect_Or_Pragma
            & " Skip_Proof cannot occur in the scope of a"
            & " Skip_Flow_And_Proof aspect or pragma",
            Prag);
      end if;

      if not Is_Generic_Unit (E) then
         if Name = "skip_proof" then
            Skip_Proof_Annotations.Insert (E);
         else
            Skip_Flow_And_Proof_Annotations.Insert (E);
         end if;
      end if;
   end Check_Skip_Annotations;

   --------------------
   -- Error_Msg_N_If --
   --------------------

   procedure Error_Msg_N_If
     (Msg           : String;
      N             : Node_Or_Entity_Id;
      Names         : Node_Lists.List := Node_Lists.Empty;
      Kind          : Msg_Severity := Error_Kind;
      Continuations : Message_Lists.List := Message_Lists.Empty) is
   begin
      if Emit_Messages then
         Error_Msg_N
           (Errout_Wrapper.Create (Msg, Names => Names),
            N,
            Kind          => Kind,
            Continuations => Continuations);
      end if;
   end Error_Msg_N_If;

   ---------------------
   -- Error_Msg_NE_If --
   ---------------------

   procedure Error_Msg_NE_If
     (Msg           : String;
      N             : Node_Or_Entity_Id;
      E             : Node_Or_Entity_Id;
      Kind          : Msg_Severity := Error_Kind;
      Continuations : Message_Lists.List := Message_Lists.Empty) is
   begin
      Error_Msg_N_If
        (Msg, N, Names => [E], Kind => Kind, Continuations => Continuations);
   end Error_Msg_NE_If;

   ----------------------------------------------
   -- Set_Has_No_Bitwise_Operations_Annotation --
   ----------------------------------------------

   procedure Set_Has_No_Bitwise_Operations_Annotation (E : Entity_Id) is
   begin
      No_Bitwise_Operations_Annotations.Include (Unique_Entity (E));
   end Set_Has_No_Bitwise_Operations_Annotation;

   ---------------------------------------
   -- Set_Has_No_Wrap_Around_Annotation --
   ---------------------------------------

   procedure Set_Has_No_Wrap_Around_Annotation (E : Entity_Id) is
   begin
      No_Wrap_Around_Annotations.Include (Unique_Entity (E));
   end Set_Has_No_Wrap_Around_Annotation;

   ----------------------
   -- Warning_Msg_N_If --
   ----------------------

   procedure Warning_Msg_N_If
     (Kind          : Misc_Warning_Kind;
      N             : Node_Or_Entity_Id;
      Names         : Node_Lists.List := Node_Lists.Empty;
      Continuations : Message_Lists.List := Message_Lists.Empty) is
   begin
      if Emit_Messages then
         Warning_Msg_N
           (Kind, N, Names => Names, Continuations => Continuations);
      end if;
   end Warning_Msg_N_If;

end SPARK_Definition.Annotate;
