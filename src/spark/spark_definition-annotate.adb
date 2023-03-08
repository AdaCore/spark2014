------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--              S P A R K _ D E F I N I T I O N - A N N O T A T E           --
--                                                                          --
--                                  B o d y                                 --
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

with Ada.Characters.Handling;      use Ada.Characters.Handling;
with Ada.Containers.Hashed_Maps;
with Ada.Containers.Doubly_Linked_Lists;
with Aspects;                      use Aspects;
with Checked_Types;                use Checked_Types;
with Common_Containers;
with Errout;                       use Errout;
with Erroutc;
with Flow_Types;                   use Flow_Types;
with Flow_Utility;                 use Flow_Utility;
with Gnat2Why_Args;
with Namet;                        use Namet;
with Nlists;                       use Nlists;
with Sem_Aux;                      use Sem_Aux;
with Sem_Ch12;
with Sinfo.Utils;                  use Sinfo.Utils;
with Sinput;                       use Sinput;
with Snames;                       use Snames;
with SPARK_Definition.Violations;  use SPARK_Definition.Violations;
with SPARK_Util.Subprograms;       use SPARK_Util.Subprograms;
with SPARK_Util.Types;             use SPARK_Util.Types;
with Stand;                        use Stand;
with Stringt;                      use Stringt;
with String_Utils;                 use String_Utils;
with VC_Kinds;                     use VC_Kinds;

package body SPARK_Definition.Annotate is

   package Annot_Ranges is new Ada.Containers.Doubly_Linked_Lists
     (Element_Type => Annotated_Range);
   --  ??? why not use Ordered_Sets here?

   function "<" (L, R : Annotated_Range) return Boolean;
   --  Ordering relation on annotated ranges; used only for assertions

   package Annot_Range_Sorting is new Annot_Ranges.Generic_Sorting;
   --  Sorting of annotated ranges; used only to assert that data in the
   --  container is indeed sorted.

   package Iterable_Maps is new Ada.Containers.Hashed_Maps
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

   Always_Return_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores subprogram and package entities with a pragma Annotate
   --  (GNATprove, Always_Return, E).

   At_End_Borrow_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores function entities with a pragma Annotate
   --  (GNATprove, At_End_Borrow, E).

   Automatic_Instantiation_Annotations : Common_Containers.Node_Maps.Map :=
     Common_Containers.Node_Maps.Empty_Map;
   --  Maps lemma procedures annotated with Automatic_Instantiation to their
   --  associated function.

   Delayed_Checks_For_Lemmas : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Set of lemmas with automatic instantiation that need to be checked

   Delayed_HO_Specialization_Checks : Common_Containers.Node_Maps.Map :=
     Common_Containers.Node_Maps.Empty_Map;
   --  Maps calls to functions which were not marked yet but should be
   --  annotated with Higher_Order_Specialization to the node on which the
   --  checks shall be emited.

   Higher_Order_Spec_Annotations : Common_Containers.Node_Graphs.Map :=
     Common_Containers.Node_Graphs.Empty_Map;
   --  Stores function entities with a pragma Annotate
   --  (GNATprove, Higher_Order_Specialization, E). They are mapped to a
   --  (possibly empty) set of  lemmas that should be automatically
   --  instantiated when the function is specialized.

   package Node_To_Node_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Node_Maps.Map,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => Node_Maps."=");
   --  Maps of nodes to maps of nodes to nodes

   Higher_Order_Lemma_Specializations : Node_To_Node_Maps.Map :=
     Node_To_Node_Maps.Empty_Map;
   --  Maps lemma procedures to the mapping that should be used to construct
   --  their specialization from their associated function specialization.

   Inline_Annotations : Common_Containers.Node_Maps.Map :=
     Common_Containers.Node_Maps.Empty_Map;
   --  Maps all the function entities E with a pragma Annotate
   --  (GNATprove, Inline_For_Proof, E) to their expression.
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

   Might_Not_Return_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores procedure entities with a pragma Annotate
   --  (GNATprove, Might_Not_Return, E).

   No_Wrap_Around_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores type entities with a pragma Annotate
   --  (GNATprove, No_Wrap_Around, E).

   type Ownership_Annotation (Needs_Reclamation : Boolean := False) is record
      case Needs_Reclamation is
         when True =>
            Check_Function : Entity_Id := Empty;
            Reclaimed      : Boolean := False;
         when False =>
            null;
      end case;
   end record;

   package Node_To_Ownership_Maps is new Ada.Containers.Hashed_Maps
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
   --  Needs_Reclamation functions).

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
         when False => null;
         when True =>
            Kind    : Annotate_Kind;
            Pattern : String_Id;
            Reason  : String_Id;
      end case;
   end record;

   procedure Check_Pragma_Annotate_GNATprove
     (Prag   : Node_Id;
      Result : out Check_Justification)
   with Pre => Is_Pragma_Annotate_GNATprove (Prag);
   --  Check validity of the pragma Annotate (GNATprove, ...). For annotations
   --  used to justify check messages, fill in the kind, pattern and reason of
   --  the pragma in Result. Result.Present is False if some syntax error
   --  has been detected, or if the pragma Annotate is not used for
   --  justification purposes.

   procedure Check_Automatic_Inst_And_HO_Specialization_Compatibility
     (Lemma : Subprogram_Kind_Id;
      Fun   : Function_Kind_Id)
   with Pre => Has_Automatic_Instantiation_Annotation (Lemma)
     and then Retrieve_Automatic_Instantiation_Annotation (Lemma) = Fun
     and then Has_Higher_Order_Specialization_Annotation (Fun);
   --  Check that lemmas associated to a function with higher order
   --  specialization can be specialized with the function. If it is not the
   --  case, emit a warning. Store compatible lemmas in the
   --  Higher_Order_Spec_Annotation map and their parameter associations in
   --  Higher_Order_Lemma_Specializations.

   procedure Check_Automatic_Instantiation_Annotation
     (Arg3_Exp : Node_Id;
      Prag     : Node_Id)
   with Pre => Present (Arg3_Exp);
   --  Check validity of a pragma Annotate (GNATprove, Automatic_Instantiation,
   --  E) and insert it in the Automatic_Instantiation_Annotations map.

   procedure Check_Always_Return_Annotation
     (Arg3_Exp : Node_Id;
      Prag     : Node_Id)
   with Pre => Present (Arg3_Exp);
   --  Check validity of a pragma Annotate (GNATprove, Always_Return, E) and
   --  insert it in the Always_Return_Annotations map.

   procedure Check_At_End_Borrow_Annotation (Arg3_Exp : Node_Id) with
     Pre => Present (Arg3_Exp);
   --  Check validity of a pragma Annotate (GNATprove, At_End_Borrow, E) and
   --  insert it in the At_End_Borrow_Annotations map.

   procedure Check_Higher_Order_Specialization_Annotation
     (Arg3_Exp : Node_Id;
      Prag     : Node_Id);
   --  Check validity of a pragma Annotate
   --  (GNATprove, Higher_Order_Specialization, E) and insert it in the
   --  Higher_Order_Spec_Annotations map.

   procedure Check_Inline_Annotation (Arg3_Exp : Node_Id; Prag : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, Inline_For_Proof, E)
   --  and insert it in the Inline_Annotations map.

   procedure Check_Iterable_Annotation
     (Arg3_Exp : Node_Id;
      Arg4_Exp : Node_Id;
      Prag : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, Iterate_For_Proof, E)
   --  and insert it in the Iterable_Annotations map.

   procedure Check_Logical_Equal_Annotation
     (Arg3_Exp : Node_Id;
      Prag     : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, Logical_Equal, E)
   --  and insert it in the Logical_Eq_Annotations set.

   procedure Check_Might_Not_Return_Annotation
     (Arg3_Exp : Node_Id;
      Prag     : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, Might_Not_Return, E)
   --  and insert it in the Might_Not_Return_Annotations map.

   procedure Check_No_Wrap_Around_Annotation (Arg3_Exp : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, No_Wrap_Around, E)
   --  and insert it in the No_Wrap_Around_Annotations map.

   procedure Check_Ownership_Annotation
     (Aspect_Or_Pragma : String;
      Arg3_Exp         : Node_Id;
      Arg4_Exp         : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, Ownership, ???, E)
   --  and update the Ownership_Annotations map.

   ---------
   -- "<" --
   ---------

   function "<" (L, R : Annotated_Range) return Boolean is
   begin
      return L.First < R.First;
   end "<";

   ------------------------------------
   -- Check_Always_Return_Annotation --
   ------------------------------------

   procedure Check_Always_Return_Annotation
     (Arg3_Exp : Node_Id;
      Prag     : Node_Id)
   is
      From_Aspect      : constant Boolean := From_Aspect_Specification (Prag);
      Aspect_Or_Pragma : constant String :=
        (if From_Aspect then "aspect" else "pragma");
      E : Entity_Id;

   begin
      --  The third argument must be an entity

      if Nkind (Arg3_Exp) not in N_Has_Entity then
         Error_Msg_N
           ("third argument of pragma Annotate Always_Return must be "
            & "an entity",
            Arg3_Exp);
         return;
      end if;

      E := Entity (Arg3_Exp);
      pragma Assert (Present (E));

      --  This entity must be a subprogram or a package

      if Ekind (E) not in
        Subprogram_Kind | E_Package | Generic_Unit_Kind
      then
         Error_Msg_N
           ("Entity parameter of a pragma Always_Return must be a subprogram "
            & "or a package",
            Arg3_Exp);
         return;

      --  It must not be a procedure with No_Return

      elsif No_Return (E) then
         Error_Msg_N
           ("procedure with " & Aspect_Or_Pragma & " Annotate "
            & "Always_Return must not also be marked with No_Return",
            Arg3_Exp);

      --  It must not be a procedure with Might_Not_Return

      elsif Ekind (E) in E_Procedure | E_Generic_Procedure
        and then Has_Might_Not_Return_Annotation (E)
      then
         Error_Msg_N
           ("procedure with " & Aspect_Or_Pragma & " Annotate "
            & "Always_Return must not also be marked with Might_Not_Return",
            Arg3_Exp);
      end if;

      --  Go through renamings to find the appropriate entity

      Always_Return_Annotations.Include (Get_Renamed_Entity (E));
   end Check_Always_Return_Annotation;

   ------------------------------------
   -- Check_At_End_Borrow_Annotation --
   ------------------------------------

   procedure Check_At_End_Borrow_Annotation (Arg3_Exp : Node_Id) is

      procedure Check_At_End_Borrow_Entity (E : Entity_Id);
      --  E should be a ghost identity expression function taking (and
      --  returning) an access-to-constant type.

      --------------------------------
      -- Check_At_End_Borrow_Entity --
      --------------------------------

      procedure Check_At_End_Borrow_Entity (E : Entity_Id) is
         Path      : constant Entity_Id := First_Formal (E);
         Contracts : constant Node_Id := Contract (E);
      begin
         if No (Path)
           or else Present (Next_Formal (Path))
         then
            Error_Msg_N
              ("At_End_Borrow function must have exactly one parameter", E);
         elsif not Is_Anonymous_Access_Type (Etype (Path))
           or else not Is_Access_Constant (Etype (Path))
         then
            Error_Msg_N
              ("the parameter of an At_End_Borrow function must have an"
               & " anonymous access-to-constant type", E);
         elsif not Is_Anonymous_Access_Type (Etype (E))
           or else not Is_Access_Constant (Etype (E))
         then
            Error_Msg_N
              ("At_End_Borrow function must return an"
               & " anonymous access-to-constant type", E);
         elsif not Is_Ghost_Entity (E) then
            Error_Msg_N
              ("At_End_Borrow function must be a ghost function", E);
         elsif Present (Contracts)
           and then (Present (Pre_Post_Conditions (Contracts)) or else
                     Present (Contract_Test_Cases (Contracts)))
         then
            Error_Msg_N
              ("At_End_Borrow function should not have a contract", E);
         elsif not Is_Expression_Function_Or_Completion (E) then
            Error_Msg_N
              ("At_End_Borrow function must be an expression function", E);
         else
            declare
               Expr : constant Node_Id :=
                 Expression (Get_Expression_Function (E));
            begin
               if Nkind (Original_Node (Expr)) not in
                   N_Expanded_Name | N_Identifier
                 or else Entity (Original_Node (Expr)) /= Path
               then
                  Error_Msg_N
                    ("At_End_Borrow function must be the identity function",
                     E);
               end if;
            end;
         end if;
      end Check_At_End_Borrow_Entity;

      E : Entity_Id;

   --  Start of processing for Check_At_End_Borrow_Annotation

   begin
      if Nkind (Arg3_Exp) not in N_Has_Entity then
         Error_Msg_N
           ("third parameter of a pragma At_End_Borrow must be an entity",
            Arg3_Exp);
         return;
      else
         E := Entity (Arg3_Exp);
      end if;

      --  This entity must be a function

      if Ekind (E) /= E_Function then
         Error_Msg_N
           ("entity parameter of a pragma At_End_Borrow must be a function",
            Arg3_Exp);
         return;
      else
         Check_At_End_Borrow_Entity (E);
      end if;

      --  Go through renamings to find the appropriate entity

      At_End_Borrow_Annotations.Include (Get_Renamed_Entity (E));
   end Check_At_End_Borrow_Annotation;

   --------------------------------------------------------------
   -- Check_Automatic_Inst_And_HO_Specialization_Compatibility --
   --------------------------------------------------------------

   procedure Check_Automatic_Inst_And_HO_Specialization_Compatibility
     (Lemma : Subprogram_Kind_Id;
      Fun   : Function_Kind_Id)
   is
   begin
      --  Lemma shall to be annotated with higher order specialization

      if not Has_Higher_Order_Specialization_Annotation (Lemma) then
         Error_Msg_N
           ("?automatically instantiated lemma is not annotated with"
            & " Higher_Order_Specialization",
            Lemma);
         Error_Msg_NE
           ("\it will not be automatically instantiated on specializations"
            & " of &",
            Lemma, Fun);
         return;
      end if;

      --  Go over the contracts of Lemma to make sure that:
      --   * they contain at least one specializable call to Fun,
      --   * they do not contain partially specializable calls to Fun, and
      --   * all specializable calls to Fun in the contracts of Lemma have
      --     the same specialization.

      declare
         Lemma_Params  : Node_Maps.Map;
         --  Map used to simulate a specialized call to Lemma. It will map
         --  its specializable formals to themselves.

         Nb_Fun_Params : Integer := 0;
         --  Number of the specializable parameters of Fun

         Spec_Params   : Node_Maps.Map;
         Violation     : Boolean := False;

         function Check_Calls_To_Fun (N : Node_Id) return Traverse_Result;
         --  Return Abandon if N is a non conforming call to Fun. A warning
         --  will have been emitted in this case and Violation will be set to
         --  True. Otherwise, if N is a call to Fun, the Spec_Params map will
         --  be filled with the mapping for the parameters of Fun and OK is
         --  returned.

         function Check_Calls_To_Fun (N : Node_Id) return Traverse_Result is
            Call_Params : Node_Maps.Map;
         begin
            if Nkind (N) = N_Function_Call
              and then Get_Called_Entity (N) = Fun
            then
               Call_Params := Get_Specialized_Parameters (N, Lemma_Params);

               declare
                  use type Node_Maps.Map;
                  Statically_Specialized_Call : constant Boolean :=
                    (for all E of Call_Params =>
                        not Lemma_Params.Contains (E));
                  --  No specialized parameter of N depends of the parameters
                  --  of Lemma.
                  Totally_Specialized_Call   : constant Boolean :=
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
                     Error_Msg_NE
                       ("?automatically instantiated lemma contains calls to "
                        & "& which cannot be arbitrarily specialized",
                        Lemma, Fun);
                     Error_Msg_NE
                       ("\it will not be automatically instantiated on"
                        & " specializations of &",
                        Lemma, Fun);
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
                     Error_Msg_NE
                       ("?automatically instantiated lemma contains several "
                        & "calls to & with different specializations",
                        Lemma, Fun);
                     Error_Msg_NE
                       ("\it will not be automatically instantiated on"
                        & " specializations of &",
                        Lemma, Fun);

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
            Pre      : constant Node_Lists.List := Find_Contracts
              (Lemma, Pragma_Precondition, False, False);
            Post     : constant Node_Lists.List := Find_Contracts
              (Lemma, Pragma_Postcondition, False, False);
            CC       : constant Node_Id :=
              Get_Pragma (Lemma, Pragma_Contract_Cases);
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
            Check_Contract_Of_Lemma (CC);
         end;

         <<Violation_Found>>

         --  If Violation is True, a warning has been emitted already. Exit
         --  the function.

         if Violation then
            return;

         --  Check that the lemma contains at least a call to Fun

         elsif Spec_Params.Is_Empty then
            Error_Msg_NE
              ("?automatically instantiated lemma does not contain any "
               & "specializable calls to &",
               Lemma, Fun);
            Error_Msg_NE
              ("\it will not be automatically instantiated on"
               & " specializations of &",
               Lemma, Fun);
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
     (Arg3_Exp : Node_Id;
      Prag     : Node_Id)
   is
      From_Aspect      : constant Boolean := From_Aspect_Specification (Prag);
      Aspect_Or_Pragma : constant String :=
        (if From_Aspect then "aspect" else "pragma");
      E : Entity_Id;
   begin
      --  The third argument must be an entity

      if Nkind (Arg3_Exp) not in N_Has_Entity then
         Error_Msg_N
           ("third argument of pragma Annotate Automatic_Instantiation must be"
            & " an entity",
            Arg3_Exp);
         return;
      end if;

      E := Entity (Arg3_Exp);
      pragma Assert (Present (E));

      --  This entity must be a ghost procedure

      if Ekind (E) /= E_Procedure then
         Error_Msg_N
           ("entity annotated with the " & Aspect_Or_Pragma
            & " Automatic_Instantiation must be a procedure",
            Arg3_Exp);
         return;
      elsif not Is_Ghost_Entity (E) then
         Error_Msg_N
           ("procedure annotated with the " & Aspect_Or_Pragma
            & " Automatic_Instantiation must be ghost",
            E);
         return;
      end if;

      --  It shall not have mutable parameters

      declare
         Formal : Entity_Id := First_Formal (E);
      begin
         while Present (Formal) loop
            if Ekind (Formal) /= E_In_Parameter
              or else (Is_Access_Object_Type (Etype (Formal))
                       and then not Is_Access_Constant (Etype (Formal)))
            then
               declare
                  Param_String : constant String :=
                    (case Ekind (Formal) is
                        when E_In_Out_Parameter =>
                          """in out"" parameters",
                        when E_Out_Parameter =>
                          """out"" parameters",
                        when E_In_Parameter =>
                          "parameters of an access-to-variable type",
                        when others =>
                           raise Program_Error);
               begin
                  Error_Msg_N
                    ("procedure annotated with the " & Aspect_Or_Pragma
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
            Use_Deduced_Globals =>
               not Gnat2Why_Args.Global_Gen_Mode,
            Ignore_Depends      => False);

         if not Globals.Outputs.Is_Empty then
            Error_Msg_N
              ("procedure annotated with the " & Aspect_Or_Pragma
               & " Automatic_Instantiation shall not have global"
               & " outputs", E);
            return;
         end if;
      end;

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
               Error_Msg_N
                 ("procedure annotated with the " & Aspect_Or_Pragma
                  & " Automatic_Instantiation shall be declared directly"
                  & " after a function", E);
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
                  --  Lemmas cannot be associated to volatile functions

                  if Ekind (Prec) = E_Function
                    and then Is_Volatile_Function (Prec)
                  then
                     Error_Msg_N
                       ("procedure annotated with the " & Aspect_Or_Pragma
                        & " Automatic_Instantiation shall not be declared"
                        & " after a volatile function", E);
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
                    and then Is_Pragma_Annotate_Automatic_Instantiation
                      (AI_Pragma, Prec)
                  then
                     pragma Assert (Ekind (Prec) = E_Procedure);
                     AI_Pragma := Empty;

                  --  Lemmas cannot be associated to procedures

                  else
                     Error_Msg_N
                       ("procedure annotated with the " & Aspect_Or_Pragma
                        & " Automatic_Instantiation shall not be declared"
                        & " after a procedure", E);
                     return;
                  end if;
               end;

            --  The declaration before E is not a function declaration

            else
               Error_Msg_N
                 ("procedure annotated with the " & Aspect_Or_Pragma
                  & " Automatic_Instantiation shall be declared directly"
                  & " after a function", E);
               return;
            end if;
         end loop;
      end;
   end Check_Automatic_Instantiation_Annotation;

   --------------------------------------------------
   -- Check_Higher_Order_Specialization_Annotation --
   --------------------------------------------------

   procedure Check_Higher_Order_Specialization_Annotation
     (Arg3_Exp : Node_Id;
      Prag     : Node_Id)
   is
      From_Aspect      : constant Boolean := From_Aspect_Specification (Prag);
      Aspect_Or_Pragma : constant String :=
        (if From_Aspect then "aspect" else "pragma");
      E                : Entity_Id;
   begin
      --  The third argument must be an entity

      if Nkind (Arg3_Exp) not in N_Has_Entity then
         Error_Msg_N
           ("third argument of pragma Annotate Higher_Order_Specialization "
            & "must be an entity",
            Arg3_Exp);
         return;
      end if;

      E := Entity (Arg3_Exp);

      --  This entity must be a function

      if Ekind (E) not in E_Procedure | E_Function then
         Error_Msg_N
           (Aspect_Or_Pragma & " Higher_Order_Specialization must be applied"
            & " to a function or a lemma procedure",
            Arg3_Exp);
         return;

      --  For now reject volatile functions, dispatching operations, and
      --  borrowing traversal functions.

      elsif Ekind (E) = E_Function and then Is_Volatile_Function (E) then
         Error_Msg_N
           ("function annotated with Higher_Order_Specialization shall not be"
            & " a volatile function",
            Arg3_Exp);
         return;
      elsif Einfo.Entities.Is_Dispatching_Operation (E)
        and then Present (SPARK_Util.Subprograms.Find_Dispatching_Type (E))
      then
         Error_Msg_N
           ("subprogram annotated with Higher_Order_Specialization shall not"
            & " be a dispatching operation",
            Arg3_Exp);
         return;
      elsif Is_Borrowing_Traversal_Function (E) then
         Error_Msg_N
           ("function annotated with Higher_Order_Specialization shall not be"
            & " a borrowing traversal function",
            Arg3_Exp);
         return;

      --  For procedures, check that we have a lemma

      elsif Ekind (E) = E_Procedure then

         --  It should be ghost

         if not Is_Ghost_Entity (E) then
            Error_Msg_N
              ("procedure annotated with the " & Aspect_Or_Pragma
               & " Higher_Order_Specialization shall be ghost",
               E);
            return;
         end if;

         --  It shall not have mutable parameters

         declare
            Formal : Entity_Id := First_Formal (E);
         begin
            while Present (Formal) loop
               if Ekind (Formal) /= E_In_Parameter
                 or else (Is_Access_Object_Type (Etype (Formal))
                          and then not Is_Access_Constant (Etype (Formal)))
               then
                  declare
                     Param_String : constant String :=
                       (case Ekind (Formal) is
                           when E_In_Out_Parameter =>
                             """in out"" parameters",
                           when E_Out_Parameter    =>
                             """out"" parameters",
                           when E_In_Parameter     =>
                             "parameters of an access-to-variable type",
                           when others             =>
                              raise Program_Error);
                  begin
                     Error_Msg_N
                       ("procedure annotated with the " & Aspect_Or_Pragma
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
               Use_Deduced_Globals =>
                  not Gnat2Why_Args.Global_Gen_Mode,
               Ignore_Depends      => False);

            if not Globals.Outputs.Is_Empty then
               Error_Msg_N
                 ("procedure annotated with the " & Aspect_Or_Pragma
                  & " Higher_Order_Specialization shall not have global"
                  & " outputs", E);
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
         Error_Msg_N
           ("function annotated with both Higher_Order_Specialization and"
            & " Inline_For_Proof shall have a postcondition",
            E);
         return;
      end if;

      declare
         F         : Opt_Formal_Kind_Id := First_Formal (E);
         Formals   : Entity_Sets.Set;
         Violation : Node_Id := Empty;

         function Is_Use_Of_Formal (N : Node_Id) return Traverse_Result is
           (if Nkind (N) in N_Expanded_Name | N_Identifier
              and then Formals.Contains (Unique_Entity (Entity (N)))
            then Abandon else OK);

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
           (N : Node_Id) return Traverse_Result
         is
         begin
            --  Uses are allowed under dereferences

            if Nkind (N) = N_Explicit_Dereference
              and then Nkind (Prefix (N)) in
                N_Expanded_Name | N_Identifier
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
                    or else Nkind (Call) not in N_Function_Call
                                              | N_Procedure_Call_Statement
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

                     elsif not
                       Has_Higher_Order_Specialization_Annotation (Callee)
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
            Error_Msg_N
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
            Pre      : constant Node_Lists.List := Find_Contracts
              (E, Pragma_Precondition, False, False);
            Post     : constant Node_Lists.List := Find_Contracts
              (E, Pragma_Postcondition, False, False);
            CC       : constant Node_Id :=
              Get_Pragma (E, Pragma_Contract_Cases);
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
            Find_Unsupported_Use_Of_Formal (CC);
            Find_Unsupported_Use_Of_Formal (Variants);
         end;

         <<Violation_Found>>
         if Present (Violation) then
            if Nkind (Violation) = N_Iterated_Component_Association then
               Error_Msg_N
                 ("subprogram annotated with Higher_Order_Specialization"
                  & " shall not reference its access-to-function"
                  & " parameters inside an iterated component association",
                  Violation);
            else
               Error_Msg_N
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

      Higher_Order_Spec_Annotations.Include (E, Node_Sets.Empty_Set);
   end Check_Higher_Order_Specialization_Annotation;

   -----------------------------
   -- Check_Inline_Annotation --
   -----------------------------

   procedure Check_Inline_Annotation (Arg3_Exp : Node_Id; Prag : Node_Id) is
      E     : Entity_Id;
      Nodes : Common_Containers.Node_Lists.List;
      Value : Node_Id;

      package NL renames Common_Containers.Node_Lists;

      use type Ada.Containers.Count_Type;

   begin
      --  The third argument must be an entity

      if Nkind (Arg3_Exp) not in N_Has_Entity then
         Error_Msg_N
           ("third argument of pragma Annotate Inline_For_Proof must be "
            & "an entity",
            Arg3_Exp);
         return;
      end if;

      E := Entity (Arg3_Exp);

      --  This entity must be a function

      if Ekind (E) /= E_Function then
         Error_Msg_N
           ("Entity parameter of a pragma Inline_For_Proof must be a function",
            Arg3_Exp);
         return;
      end if;

      --  Check if E has a postcondition

      Nodes := Find_Contracts (E, Pragma_Postcondition, False, False);

      --  If it does not have one, it must be an expression function

      if Nodes.Is_Empty then
         if not Is_Expression_Function_Or_Completion (E) then
            Error_Msg_N
              ("function with Inline_For_Proof and no postconditions must "
               & "be an expression function", E);
            return;
         elsif not SPARK_Definition.Entity_Body_Compatible_With_SPARK (E) then
            Mark_Violation
              ("expression function with Inline_For_Proof whose body is"
               & " not in SPARK", E);
            return;
         else
            Value := Expression (Get_Expression_Function (E));
         end if;

      elsif Nodes.Length > 1 then
         Error_Msg_N
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

         --  Or the equality operator has been rewritten into a function call

         elsif Nkind (Value) = N_Function_Call
           and then Nkind (Original_Node (Value)) = N_Op_Eq
           and then Is_Attribute_Result (Left_Opnd (Original_Node (Value)))
         then
            Value := Next_Actual (First_Actual (Value));

         else
            Error_Msg_NE
              ("function with Inline_For_Proof must"
               & " have a postcondition of the form `&''Result = Expr`", E, E);
            return;
         end if;
      end if;

      --  Inline_For_Proof and Logical_Equal are incompatible

      if Has_Logical_Eq_Annotation (E) then
         Error_Msg_N
           ("Entity parameter of a pragma Inline_For_Proof shall not have a"
            & " Logical_Equal annotation", Arg3_Exp);
         return;
      end if;

      --  The body of expression functions is ignored for higher order
      --  specialization. Require a postcondition.

      if Has_Higher_Order_Specialization_Annotation (E) and then Nodes.Is_Empty
      then
         Error_Msg_N
           ("function annotated with both Higher_Order_Specialization and"
            & " Inline_For_Proof shall have a postcondition",
            E);
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
      Found : out Boolean;
      Info  : out Annotated_Range)
   is
      Node_Slc : constant Source_Ptr := Sloc (Node);
   begin
      Found := False;

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
           and then Erroutc.Matches (S => Msg,
                                     P => '*' & String_Value (E.Pattern) & '*')
         then
            Info := E;
            Found := True;

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
     (Arg3_Exp : Node_Id;
      Arg4_Exp : Node_Id;
      Prag     : Node_Id)
   is

      procedure Check_Common_Properties
        (Container_Ty   : Type_Kind_Id;
         E              : Entity_Id;
         Ok             : in out Boolean;
         Name_For_Error : String);
      --  Checks that are common for Model/Contains function:
      --  No Globals, not volatile, primitive.

      procedure Check_Contains_Entity
        (E            : Entity_Id;
         Ok           : in out Boolean;
         Cont_Element : out Entity_Id);
      --  Checks that E is a valid Contains function for a type with an
      --  Iterable aspect. Initializes Cont_Element correctly if succeeding.

      procedure Check_Model_Entity
        (E            : Entity_Id;
         Ok           : in out Boolean;
         Cont_Element : out Entity_Id);
      --  Checks that E is a valid Model function for a type with an
      --  Iterable aspect. Initializes Cont_Element correctly if succeeding.

      function Find_Model_Root (Container_Type : Entity_Id) return Entity_Id;
      --  Computes the final container type at the end of the
      --  model chain for the currently known Iterable_For_Proof(...,"Model")
      --  annotations.

      procedure Process_Iterable_Annotation
        (Kind   : Iterable_Kind;
         Entity : Entity_Id);
      --  Insert an iterable annotation into the Iterable_Annotations map and
      --  mark the iterable functions.

      -----------------------------
      -- Check_Common_Properties --
      -----------------------------

      procedure Check_Common_Properties
        (Container_Ty   : Type_Kind_Id;
         E              : Entity_Id;
         Ok             : in out Boolean;
         Name_For_Error : String)
      is
         Globals : Global_Flow_Ids;
      begin
         Ok := False;
         if Scope (E) /= Scope (Container_Ty) then
            Error_Msg_N
              (Name_For_Error
               & " function must be primitive for container type", E);
            return;
         end if;
         if Is_Volatile_Function (E) then
            Error_Msg_N
              (Name_For_Error & " function must not be volatile", E);
            return;
         end if;
         Get_Globals
           (Subprogram          => E,
            Scope               =>
              (Ent => E, Part => Visible_Part),
            Classwide           => False,
            Globals             => Globals,
            Use_Deduced_Globals =>
               not Gnat2Why_Args.Global_Gen_Mode,
            Ignore_Depends      => False);
         if not Globals.Proof_Ins.Is_Empty
           or else not Globals.Inputs.Is_Empty
           or else not Globals.Outputs.Is_Empty
         then
            Error_Msg_N
              (Name_For_Error
               & " function shall not access global data", E);
            return;
         else
            Ok := True;
         end if;
      end Check_Common_Properties;

      ---------------------------
      -- Check_Contains_Entity --
      ---------------------------

      procedure Check_Contains_Entity
        (E            : Entity_Id;
         Ok           : in out Boolean;
         Cont_Element : out Entity_Id) is
         C_Param : constant Node_Id := First_Formal (E);
         E_Param : constant Node_Id :=
           (if Present (C_Param) then Next_Formal (C_Param) else Empty);
      begin
         if No (E_Param) or else Present (Next_Formal (E_Param)) then
            Error_Msg_N
              ("Contains function must have exactly two parameters", E);
         elsif not Is_Standard_Boolean_Type (Etype (E)) then
            Error_Msg_N
              ("Contains function must return Booleans", E);
         else
            declare
               Container_Type : constant Entity_Id := Etype (C_Param);
               --  Type of the first argument of the Contains function

               Element_Type   : constant Entity_Id := Etype (E_Param);
               --  Type of the second argument of the Contains function

            begin
               Cont_Element :=
                 Get_Iterable_Type_Primitive (Container_Type, Name_Element);
               --  Element primitive of Container_Type
               if No (Cont_Element) then
                  Error_Msg_N
                    ("first parameter of Contains function must allow for of "
                     & "iteration", C_Param);
               elsif not In_SPARK (Cont_Element) then
                  Error_Msg_N
                    ("first parameter of Contains functions must allow for of "
                     & "iteration in SPARK", C_Param);
               elsif Retysp (Etype (Cont_Element)) /= Retysp (Element_Type)
               then
                  Error_Msg_N
                    ("second parameter of Contains must have the type of "
                     & "elements", E_Param);
               else
                  Check_Common_Properties (Container_Type, E, Ok, "Contains");
               end if;
            end;
         end if;
      end Check_Contains_Entity;

      ------------------------
      -- Check_Model_Entity --
      ------------------------

      procedure Check_Model_Entity
        (E            : Entity_Id;
         Ok           : in out Boolean;
         Cont_Element : out Entity_Id) is
         Param : constant Node_Id := First_Formal (E);
      begin
         if No (Param) or else Present (Next_Formal (Param)) then
            Error_Msg_N
              ("Model function must have exactly one parameter", E);
         else
            declare
               Container_Type : constant Entity_Id := Etype (Param);
               --  Type of first argument of the model function

               Model_Type     : constant Entity_Id := Etype (E);
               --  Return type of the model function

               Model_Element  : constant Entity_Id :=
                 Get_Iterable_Type_Primitive (Model_Type, Name_Element);
               --  Element primitive of Model_Type

            begin
               Cont_Element :=
                 Get_Iterable_Type_Primitive (Container_Type, Name_Element);
               if No (Cont_Element) then
                  Error_Msg_N
                    ("parameter of Model function must allow for of iteration",
                     Param);
               elsif not In_SPARK (Cont_Element) then
                  Error_Msg_N
                    ("parameter of Model function must allow for of iteration "
                       & "in SPARK", Param);
               elsif No (Model_Element) then
                  Error_Msg_N
                    ("return type of Model function must allow for of "
                     & "iteration", E);
               elsif not In_SPARK (Model_Element) then
                  Error_Msg_N
                    ("return type of Model function must allow for of "
                     & "iteration in SPARK", E);
               elsif Retysp (Etype (Cont_Element))
                 /= Retysp (Etype (Model_Element))
               then
                  Error_Msg_N
                    ("parameter and return type of Model function must "
                     & "allow for of iteration with the same element type",
                     E);
               elsif Has_Controlling_Result (E) then
                  Error_Msg_N
                    ("Model function must not have a controlling result", E);
               else
                  Check_Common_Properties (Container_Type, E, Ok, "Model");
                  if Ok and then
                    Unchecked_Full_Type (Find_Model_Root (Model_Type)) =
                      Unchecked_Full_Type (Container_Type)
                  then
                     Ok := False;
                     Error_Msg_N
                       ("adding this Model function would produce a circular "
                        & "definition for container model", E);
                  end if;
               end if;
            end;
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
                  when Model =>
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
        (Kind   : Iterable_Kind;
         Entity : Entity_Id)
      is
         Container_Type        : constant Entity_Id :=
           Etype (First_Entity (Entity));
         Iterable_Node         : constant Node_Id :=
           Find_Value_Of_Aspect (Container_Type, Aspect_Iterable);
         Position              : Iterable_Maps.Cursor;
         Inserted              : Boolean;
      begin
         pragma Assert (Present (Iterable_Node));

         Iterable_Annotations.Insert
           (Iterable_Node,
            Iterable_Annotation'(Kind, Entity),
            Position,
            Inserted);

         if not Inserted then
            Error_Msg_NE
              ("two Iterable_For_Proof annotations for container type &",
               Entity, Container_Type);
            return;
         end if;

      end Process_Iterable_Annotation;

      Args_Str     : constant String_Id := Strval (Arg3_Exp);
      Kind         : Iterable_Kind;
      New_Prim     : Entity_Id;
      Ok           : Boolean := False;
      Cont_Element : Entity_Id;
      --  "Element" primitive for relevant container.
      --  Set at most once.

   --  Start of processing for Check_Iterable_Annotation

   begin
      --  The fourth argument must be an entity

      pragma Assert (Present (Arg4_Exp) and then Present (Entity (Arg4_Exp)));
      New_Prim := Entity (Arg4_Exp);

      if Ekind (New_Prim) /= E_Function then
         Error_Msg_N
           ("the entity of a Gnatprove Annotate Iterable_For_Proof "
            & "pragma must be a function",
            New_Prim);
         return;
      end if;

      --  Pull function specified by the annotation for translation (and report
      --  a violation this function is not in SPARK).

      if not In_SPARK (New_Prim) then
         Mark_Violation (Arg4_Exp, From => New_Prim);
         return;
      end if;

      if To_Lower (To_String (Args_Str)) = "model" then
         Kind := Model;
         Check_Model_Entity (New_Prim, Ok, Cont_Element);
      elsif To_Lower (To_String (Args_Str)) = "contains" then
         Kind := Contains;
         Check_Contains_Entity (New_Prim, Ok, Cont_Element);
      else
         Error_Msg_N
           ("the third argument of a Gnatprove Annotate Iterable_For_Proof "
            & "pragma must be Model or Contains",
            Arg3_Exp);
         return;
      end if;

      if not Ok then
         return;
      end if;

      --  Check that pragma is placed immediately after declaration
      --  of 'Element' primitive
      declare
         Cursor : Node_Id := Parent (Declaration_Node (Cont_Element));
      begin
         if Is_List_Member (Cursor)
           and then Decl_Starts_Pragma_Annotate_Range (Cursor)
         then
            Next (Cursor);
            while Present (Cursor) loop
               if Is_Pragma_Annotate_GNATprove (Cursor)
               then
                  if Cursor = Prag
                  then
                     goto Found;
                  end if;
               elsif Decl_Starts_Pragma_Annotate_Range (Cursor)
                 and then
                   Nkind (Cursor) not in N_Pragma | N_Null_Statement
               then
                  exit;
               end if;
               Next (Cursor);
            end loop;
         end if;
         Error_Msg_N ("pragma Iterable_For_Proof must immediately follow"
                      & " the declaration of the Element", Prag);
         return;
         <<Found>>
      end;

      Process_Iterable_Annotation (Kind, New_Prim);

   end Check_Iterable_Annotation;

   ------------------------------
   -- Check_Logical_Equal_Annotation --
   ------------------------------

   procedure Check_Logical_Equal_Annotation
     (Arg3_Exp : Node_Id; Prag : Node_Id)
   is
      E : Entity_Id;

   begin
      --  The third argument must be an entity

      if Nkind (Arg3_Exp) not in N_Has_Entity then
         Error_Msg_N
           ("third argument of pragma Annotate Logical_Equal must be "
            & "an entity",
            Arg3_Exp);
         return;
      end if;

      E := Entity (Arg3_Exp);

      --  This entity must be a function

      if Ekind (E) /= E_Function then
         Error_Msg_N
           ("Entity parameter of a pragma Logical_Equal must be a function",
            Arg3_Exp);
         return;
      end if;

      --  The function shall have the signature of an equality

      if No (First_Formal (E)) or else Number_Formals (E) /= 2 then
         Error_Msg_N
           ("Entity parameter of a pragma Logical_Equal shall have exactly"
            & " two parameters", E);
         return;
      elsif not Is_Standard_Boolean_Type (Etype (E)) then
         Error_Msg_N
           ("Entity parameter of a pragma Logical_Equal shall return a"
            & " Boolean", E);
         return;
      else
         declare
            First_Param : constant Formal_Kind_Id := First_Formal (E);
            Snd_Param   : constant Formal_Kind_Id := Next_Formal (First_Param);

         begin
            if Etype (First_Param) /= Etype (Snd_Param) then
               Error_Msg_N
                 ("both parameters of an equality function shall have the"
                  & " same subtype", E);
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
            Use_Deduced_Globals =>
               not Gnat2Why_Args.Global_Gen_Mode,
            Ignore_Depends      => False);

         if not Globals.Proof_Ins.Is_Empty
           or else not Globals.Inputs.Is_Empty
           or else not Globals.Outputs.Is_Empty
         then
            Error_Msg_N
              ("Entity parameter of a pragma Logical_Equal shall not access"
               & " any global data", E);
            return;
         end if;
      end;

      --  Inline_For_Proof and Logical_Equal are incompatible

      if Present (Retrieve_Inline_Annotation (E)) then
         Error_Msg_N
           ("Entity parameter of a pragma Logical_Equal shall not have an"
            & " Inline_For_Proof annotation",
            Arg3_Exp);
         return;
      end if;

      Logical_Eq_Annotations.Include (E);
      Inline_Pragmas.Include (E, Prag);
   end Check_Logical_Equal_Annotation;

   ---------------------------------------
   -- Check_Might_Not_Return_Annotation --
   ---------------------------------------

   procedure Check_Might_Not_Return_Annotation
     (Arg3_Exp : Node_Id;
      Prag     : Node_Id)
   is
      From_Aspect      : constant Boolean := From_Aspect_Specification (Prag);
      Aspect_Or_Pragma : constant String :=
        (if From_Aspect then "aspect" else "pragma");
      E                : Entity_Id;

   begin
      --  Correct number of arguments was checked before, hence third and last
      --  argument is correct in the aspect case, since it is generated.

      if Nkind (Arg3_Exp) not in N_Has_Entity then
         pragma Assert (not From_Aspect);
         Error_Msg_N
           ("third argument of pragma Annotate Might_Not_Return must be "
            & "an entity",
            Arg3_Exp);
         return;
      else
         E := Unique_Entity (Entity (Arg3_Exp));
      end if;

      --  This entity must be a (generic) procedure

      if Ekind (E) not in E_Procedure | E_Generic_Procedure then
         Error_Msg_N
           (Aspect_Or_Pragma
            & " Annotate Might_Not_Return must apply to a procedure",
            Arg3_Exp);
         return;

      --  The procedure should not be marked No_Return

      elsif No_Return (E) then
         Error_Msg_N
           ("procedure with " & Aspect_Or_Pragma & " Annotate "
            & "Might_Not_Return must not also be marked with No_Return",
            Arg3_Exp);

      --  The procedure should not be annotated as Always_Return

      elsif Has_Always_Return_Annotation (E) then
         Error_Msg_N
           ("procedure with " & Aspect_Or_Pragma & " Annotate "
            & "Might_Not_Return must not also be marked with Always_Return",
            Arg3_Exp);

      --  The procedure should not be dispatching

      elsif Is_Dispatching_Operation (E) then
         Error_Msg_N
           ("procedure with " & Aspect_Or_Pragma & " Annotate "
            & "Might_Not_Return must not also be dispatching",
            Arg3_Exp);
      end if;

      Might_Not_Return_Annotations.Include (E);
   end Check_Might_Not_Return_Annotation;

   -------------------------------------
   -- Check_No_Wrap_Around_Annotation --
   -------------------------------------

   procedure Check_No_Wrap_Around_Annotation (Arg3_Exp : Node_Id) is
      E    : Entity_Id;
      Decl : Node_Id;
      Base : Entity_Id;

   begin
      if Nkind (Arg3_Exp) not in N_Has_Entity then
         Error_Msg_N
           ("third argument of pragma Annotate No_Wrap_Around must be "
            & "an entity",
            Arg3_Exp);
         return;
      end if;

      E := Entity (Arg3_Exp);
      Decl := Parent (E);

      --  Annotation should apply to type declaration (not subtype)

      if Nkind (Decl) /= N_Full_Type_Declaration then
         Error_Msg_N
           ("Annotation No_Wrap_Around must apply to a type declaration",
            Arg3_Exp);
         return;

      --  This entity must be a modular type

      elsif not Is_Modular_Integer_Type (E) then
         Error_Msg_N
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

      Set_Has_No_Wrap_Around_Annotation (Base);
   end Check_No_Wrap_Around_Annotation;

   --------------------------------
   -- Check_Ownership_Annotation --
   --------------------------------

   procedure Check_Ownership_Annotation
     (Aspect_Or_Pragma : String;
      Arg3_Exp         : Node_Id;
      Arg4_Exp         : Node_Id)
   is
      Last_Exp  : constant Node_Id :=
        (if No (Arg4_Exp) then Arg3_Exp else Arg4_Exp);
      Extra_Exp : constant Node_Id :=
        (if No (Arg4_Exp) then Empty else Arg3_Exp);

   begin
      --  The last argument must be an entity

      if Nkind (Last_Exp) not in N_Has_Entity then
         Error_Msg_N
           ("last argument of " & Aspect_Or_Pragma
            & " Annotate Ownership must be an entity",
            Last_Exp);
         return;
      end if;

      --  The extra argument if any must be a string literal

      if Present (Extra_Exp) and then Nkind (Extra_Exp) not in N_String_Literal
      then
         Error_Msg_N
           ("third argument of " & Aspect_Or_Pragma
            & " Annotate Ownership must be a string",
            Extra_Exp);
         return;
      end if;

      declare
         Ent  : constant Entity_Id := Entity (Last_Exp);
         Kind : constant String :=
           (if No (Extra_Exp) then ""
            else To_Lower (To_String (Strval (Extra_Exp))));

      begin
         if Ekind (Ent) in Type_Kind then

            --  Check that the entity is a private type whose whose full view
            --  has SPARK_Mode => Off.

            if Ekind (Ent) not in E_Private_Type
                                | E_Record_Type_With_Private
                                | E_Limited_Private_Type
              or else Retysp (Ent) /= Ent
              or else Parent_Type (Ent) /= Ent
            then
               Error_Msg_N
                 ("a type annotated with Ownership must be"
                  & " a private type whose full view is not in SPARK",
                  Ent);

            --  pragma Annotate (GNATprove, Ownership, Ent);

            elsif No (Extra_Exp) then
               Ownership_Annotations.Insert
                 (Ent, (Needs_Reclamation => False));

            --  pragma Annotate (GNATprove, Ownership, Needs_Reclamation, Ent);

            elsif Kind = "needs_reclamation" then
               Ownership_Annotations.Insert
                 (Ent, (Needs_Reclamation => True, others => <>));

            --  Nothing else is allowed

            else
               Error_Msg_N
                 ("third argument of " & Aspect_Or_Pragma
                  & " Annotate Ownership on a type must be"
                  & " ""Needs_Reclamation""",
                  Extra_Exp);
            end if;

         elsif Ekind (Ent) = E_Function then

            --  Check that an extra parameter is provided

            if No (Extra_Exp) then
               Error_Msg_N
                 ("third argument of " & Aspect_Or_Pragma
                  & " Annotate Ownership on a"
                  & " function must be either ""Needs_Reclamation"""
                  & " or ""Is_Reclaimed""",
                  Last_Exp);

            --  Check that the function returns a boolean

            elsif Etype (Ent) /= Standard_Boolean then
               Error_Msg_N
                 ("a function annotated with Ownership must return a boolean",
                  Ent);

            --  Check that the function has only one parameter

            elsif No (First_Formal (Ent))
              or else Number_Formals (Ent) /= 1
            then
               Error_Msg_N
                 ("a function annotated with Ownership must "
                  & "have exactly one formal parameter",
                  Ent);

            else
               declare
                  G_Typ   : constant Entity_Id :=
                    Retysp (Etype (First_Formal (Ent)));
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
                     Use_Deduced_Globals =>
                        not Gnat2Why_Args.Global_Gen_Mode,
                     Ignore_Depends      => False);

                  if not Globals.Proof_Ins.Is_Empty
                    or else not Globals.Inputs.Is_Empty
                    or else not Globals.Outputs.Is_Empty
                  then
                     Error_Msg_N
                       ("a function annotated with Ownership shall"
                        & " not access any global data", Ent);

                  elsif Is_Tagged_Type (Typ)
                    and then not Is_Class_Wide_Type (G_Typ)
                  then
                     Error_Msg_N
                       ("function annotated with Ownership on a tagged type "
                        & "expects a classwide type", Ent);

                  elsif not Ownership_Annotations.Contains (Typ)
                  then
                     Error_Msg_N
                       ("the type of the first parameter of a function "
                        & "annotated with Ownership must be annotated with"
                        & " Ownership",
                        Ent);
                     Error_Msg_N
                       ("\consider annotating it with a pragma Annotate "
                        & "('G'N'A'Tprove, Ownership, ""Needs_Reclamation"""
                        & ", ...)",
                        Ent);

                  elsif not Ownership_Annotations (Typ).Needs_Reclamation then
                     Error_Msg_N
                       ("the type of the first parameter of a function "
                        & "annotated with Ownership shall need reclamation",
                        Ent);
                     Error_Msg_N
                       ("\consider annotating it with a pragma Annotate "
                        & "('G'N'A'Tprove, Ownership, ""Needs_Reclamation"""
                        & ", ...)",
                        Ent);

                  elsif Present (Ownership_Annotations (Typ).Check_Function)
                  then
                     Error_Msg_N
                       ("a single ownership function shall be supplied for a "
                        & "given type annotated with Ownership",
                        Ent);
                     Error_Msg_NE
                       ("\the function & conflicts with the current"
                        & " annotation",
                        Ent, Ownership_Annotations (Typ).Check_Function);

                  --  pragma Annotate
                  --   (GNATprove, Ownership, Needs_Reclamation, Ent);

                  elsif Kind = "needs_reclamation" then
                     Ownership_Annotations (Typ).Check_Function := Ent;
                     Ownership_Annotations (Typ).Reclaimed := False;

                  --  pragma Annotate
                  --   (GNATprove, Ownership, Is_Reclaimed, Ent);

                  elsif Kind = "is_reclaimed" then
                     Ownership_Annotations (Typ).Check_Function := Ent;
                     Ownership_Annotations (Typ).Reclaimed := True;

                  --  Nothing else is allowed

                  else
                     Error_Msg_N
                       ("third argument of " & Aspect_Or_Pragma
                        & " Annotate Ownership on a"
                        & " function must be either ""Needs_Reclamation"""
                        & " or ""Is_Reclaimed""",
                        Extra_Exp);
                  end if;
               end;
            end if;
         else
            Error_Msg_N
              ("the entity of a pragma Annotate Ownership "
               & "shall be either a type or a function",
               Ent);
         end if;
      end;
   end Check_Ownership_Annotation;

   ---------------------------------------
   -- Decl_Starts_Pragma_Annotate_Range --
   ---------------------------------------

   function Decl_Starts_Pragma_Annotate_Range (N : Node_Id) return Boolean is
     (Comes_From_Source (N)
      or else (Is_Rewrite_Substitution (N)
               and then Comes_From_Source (Original_Node (N)))
      or else (Nkind (N) in N_Subprogram_Declaration
               and then Is_Generic_Instance (Defining_Entity (N))
               and then Comes_From_Source
                           (Sem_Ch12.Get_Unit_Instantiation_Node
                              (Defining_Entity (Parent (N))))));

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
               Error_Msg_N
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
   end Do_Delayed_Checks_On_Pragma_Annotate;

   ------------------------
   -- Find_Inline_Pragma --
   ------------------------

   function Find_Inline_Pragma (E : Entity_Id) return Node_Id is
     (Inline_Pragmas.Element (E));

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
            Error_Msg_N
              (Warning_Message (Warn_Pragma_Annotate_No_Check), Prag);
         end if;
      end loop;

      for Prag of Proved_Pragma loop
         if Instantiation_Location (Sloc (Prag)) = No_Location then
            Error_Msg_N
              (Warning_Message (Warn_Pragma_Annotate_Proved_Check), Prag);
         end if;
      end loop;
   end Generate_Useless_Pragma_Annotate_Warnings;

   ------------------------------
   -- Get_Lemmas_To_Specialize --
   ------------------------------

   function Get_Lemmas_To_Specialize (E : Entity_Id) return Node_Sets.Set is
      (Higher_Order_Spec_Annotations.Element (E));

   ------------------------------------
   -- Get_Reclamation_Check_Function --
   ------------------------------------

   procedure Get_Reclamation_Check_Function
     (E              : Entity_Id;
      Check_Function : out Entity_Id;
      Reclaimed      : out Boolean)
   is
      use Node_To_Ownership_Maps;
      R : constant Entity_Id := Root_Retysp (E);
   begin
      Check_Function := Ownership_Annotations (R).Check_Function;
      Reclaimed := Ownership_Annotations (R).Reclaimed;
   end Get_Reclamation_Check_Function;

   ----------------------------------
   -- Has_Always_Return_Annotation --
   ----------------------------------

   function Has_Always_Return_Annotation (E : Entity_Id) return Boolean is
      Unit     : constant Opt_Unit_Kind_Id :=
        (if not Is_Child_Unit (E) and then Present (Scope (E))
         then Enclosing_Unit (E) else Empty);
      --  Do not look at the enclosing package for child units

      Spec     : constant Node_Id :=
        (if not Is_Generic_Instance (E) then Empty
         elsif Is_Package_Or_Generic_Package (E) then Package_Specification (E)
         else Subprogram_Specification (E));
      Gen_Unit : constant Opt_Generic_Unit_Kind_Id :=
        (if Present (Spec) and then Present (Generic_Parent (Spec))
         then Generic_Parent (Spec)
         else Empty);
      --  If E is a generic instance, also look for Always_Return annotation on
      --  the enclosing scopes of the generic unit.

   begin
      return Always_Return_Annotations.Contains (E)
        or else (Present (Unit)
                 and then Ekind (Unit) = E_Package
                 and then Has_Always_Return_Annotation (Unit))
        or else (Present (Gen_Unit)
                 and then Has_Always_Return_Annotation (Gen_Unit));
   end Has_Always_Return_Annotation;

   ----------------------------------
   -- Has_At_End_Borrow_Annotation --
   ----------------------------------

   function Has_At_End_Borrow_Annotation (E : Entity_Id) return Boolean is
     (Ekind (E) = E_Function
      and then At_End_Borrow_Annotations.Contains (E));

   --------------------------------------------
   -- Has_Automatic_Instantiation_Annotation --
   --------------------------------------------

   function Has_Automatic_Instantiation_Annotation
     (E : Entity_Id) return Boolean
   is (Automatic_Instantiation_Annotations.Contains (E));

   ------------------------------------------------
   -- Has_Higher_Order_Specialization_Annotation --
   ------------------------------------------------

   function Has_Higher_Order_Specialization_Annotation
     (E : Entity_Id) return Boolean
   is
     (Higher_Order_Spec_Annotations.Contains (E));

   -------------------------------
   -- Has_Logical_Eq_Annotation --
   -------------------------------

   function Has_Logical_Eq_Annotation (E : Entity_Id) return Boolean is
     (Ekind (E) = E_Function
      and then Logical_Eq_Annotations.Contains (E));

   -------------------------------------
   -- Has_Might_Not_Return_Annotation --
   -------------------------------------

   function Has_Might_Not_Return_Annotation (E : Entity_Id) return Boolean is
     (Ekind (E) in E_Procedure | E_Generic_Procedure
      and then Might_Not_Return_Annotations.Contains (E));

   -----------------------------------
   -- Has_No_Wrap_Around_Annotation --
   -----------------------------------

   function Has_No_Wrap_Around_Annotation (E : Entity_Id) return Boolean is
     (No_Wrap_Around_Annotations.Contains (E));

   ------------------------------
   -- Has_Ownership_Annotation --
   ------------------------------

   function Has_Ownership_Annotation (E : Entity_Id) return Boolean is
     (Ownership_Annotations.Contains (Root_Retysp (E)));

   ------------------------------------------------
   -- Is_Pragma_Annotate_Automatic_Instantiation --
   ------------------------------------------------

   function Is_Pragma_Annotate_Automatic_Instantiation
     (N : Node_Id;
      P : Entity_Id := Empty) return Boolean
   is
      Number_Of_Pragma_Args : constant Nat :=
        List_Length (Pragma_Argument_Associations (N));
      Arg1                  : constant Node_Id :=
        First (Pragma_Argument_Associations (N));
      Arg2                  : constant Node_Id := Next (Arg1);
      Name                  : constant String :=
        (if No (Arg2) then ""
         else Get_Name_String (Chars (Get_Pragma_Arg (Arg2))));
      Arg3                  : Node_Id;
      Arg3_Exp              : Node_Id := Empty;

   begin
      if Name /= "automatic_instantiation"
        or else Number_Of_Pragma_Args /= 3
      then
         return False;
      end if;

      Arg3 := Next (Arg2);
      Arg3_Exp := Expression (Arg3);
      return Nkind (Arg3_Exp) in N_Has_Entity
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
            Inline_Annotations.Include (E, Value);
         end if;
      end if;
   end Infer_Inline_Annotation;

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
         Insert_Annotate_Range (Prgma, Kind, Pattern, Reason,
                                Specification (Range_Node), Whole => True);
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

            Insert_With_Next (Prgma, Kind, Pattern, Reason, Spec_Node,
                              Skip => Range_Node);
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
         Left_Sloc := First_Sloc (Range_Node);
         Right_Sloc := First_Sloc (Prgma);
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
         New_Item => (Kind    => Kind,
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
      Insert_Annotate_Range (Prgma, Kind, Pattern, Reason, Node,
                             Whole => True);
      Next (Node);
      while Present (Node)
        and then not Comes_From_Source (Node)
        and then Nkind (Node) /= N_Expression_Function
      loop
         if Node /= Skip then
            Insert_Annotate_Range (Prgma, Kind, Pattern, Reason, Node,
                                   Whole => True);
         end if;
         Next (Node);
      end loop;
   end Insert_With_Next;

   --------------------------
   -- Mark_Pragma_Annotate --
   --------------------------

   procedure Mark_Pragma_Annotate
     (N             : Node_Id;
      Preceding     : Node_Id;
      Consider_Next : Boolean)
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
         when True =>
            if Consider_Next then
               Insert_With_Next
                 (N, Result.Kind, Result.Pattern, Result.Reason, Preceding);
            else
               Insert_Annotate_Range
                 (N, Result.Kind, Result.Pattern, Result.Reason, Preceding,
                  Whole => False);
            end if;
      end case;
   end Mark_Pragma_Annotate;

   -----------------------
   -- Needs_Reclamation --
   -----------------------

   function Needs_Reclamation (E : Entity_Id) return Boolean is
     (Ownership_Annotations (Root_Retysp (E)).Needs_Reclamation);

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
      Position : constant Common_Containers.Node_Maps.Cursor :=
        Inline_Annotations.Find (E);
   begin
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
   is
     (Higher_Order_Lemma_Specializations (E));

   -------------------------------------
   -- Check_Pragma_Annotate_GNATprove --
   -------------------------------------

   procedure Check_Pragma_Annotate_GNATprove
     (Prag   : Node_Id;
      Result : out Check_Justification)
   is
      --  Local constants

      From_Aspect      : constant Boolean := From_Aspect_Specification (Prag);
      Aspect_Or_Pragma : constant String :=
        (if From_Aspect then "aspect" else "pragma");
      Number_Of_Pragma_Args : constant Nat :=
        List_Length (Pragma_Argument_Associations (Prag));

      --  Local subprograms

      procedure Check_Argument_Number
        (Name : String;
         Num  : Pos;
         Ok   : out Boolean);
      --  Check that annotation for Name has Num arguments. Set Ok to True in
      --  that case, to False otherwise.

      function Get_Annotation_Name (Arg : Node_Id) return String;
      --  Return the name for the Annotate pragma/aspect

      ---------------------------
      -- Check_Argument_Number --
      ---------------------------

      procedure Check_Argument_Number
        (Name : String;
         Num  : Pos;
         Ok   : out Boolean)
      is
      begin
         Ok := (Num = Number_Of_Pragma_Args);

         if not Ok then
            Error_Msg_N
              ("wrong number of arguments in " & Aspect_Or_Pragma
               & " Annotate ('G'N'A'Tprove, " & Standard_Ada_Case (Name)
               & (if Num > 2 then ", ...)" else ")")
               & ", expected" & Num'Image, Prag);
         end if;
      end Check_Argument_Number;

      -------------------------
      -- Get_Annotation_Name --
      -------------------------

      function Get_Annotation_Name (Arg : Node_Id) return String is
      begin
         if No (Arg) then
            Error_Msg_N
              ("missing name in Annotate " & Aspect_Or_Pragma
               & " for 'G'N'A'Tprove", Prag);
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

      Arg3, Arg4 : Node_Id;
      Arg3_Exp, Arg4_Exp : Node_Id := Empty;
      Ok : Boolean;

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
         Error_Msg_N (Warning_Message (Warn_Pragma_External_Axiomatization),
                      Prag);
         return;

      elsif Name = "at_end_borrow"
        or else Name = "automatic_instantiation"
        or else Name = "higher_order_specialization"
        or else Name = "init_by_proof"
        or else Name = "inline_for_proof"
        or else Name = "logical_equal"
        or else Name = "might_not_return"
        or else Name = "no_wrap_around"
        or else Name = "always_return"
        or else Name = "terminating"
      then
         Check_Argument_Number (Name, 3, Ok);

      elsif Name = "iterable_for_proof"
        or else (not From_Aspect
                 and then (Name = "false_positive"
                           or else Name = "intentional"))
      then
         Check_Argument_Number (Name, 4, Ok);

      --  Ownership annotations can have 3 or 4 arguments

      elsif Name = "ownership" then
         if Number_Of_Pragma_Args <= 3 then
            Check_Argument_Number (Name, 3, Ok);
         else
            Check_Argument_Number (Name, 4, Ok);
         end if;

      --  Annotations for justifying check messages may be attached to an
      --  entity through an aspect notation, in which case a fifth generated
      --  argument denotes the entity to which the aspect applies.

      elsif From_Aspect
        and then (Name = "false_positive"
                  or else Name = "intentional")
      then
         Check_Argument_Number (Name, 5, Ok);

      else
         Error_Msg_N
           ("invalid name """ & Standard_Ada_Case (Name) & """ in "
            & Aspect_Or_Pragma & " Annotate ('G'N'A'Tprove, name)", Arg2);
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
         Check_At_End_Borrow_Annotation (Arg3_Exp);

      elsif Name = "automatic_instantiation" then
         Check_Automatic_Instantiation_Annotation (Arg3_Exp, Prag);

      elsif Name = "inline_for_proof" then
         Check_Inline_Annotation (Arg3_Exp, Prag);

      elsif Name = "higher_order_specialization" then
         Check_Higher_Order_Specialization_Annotation (Arg3_Exp, Prag);

      elsif Name = "logical_equal" then
         Check_Logical_Equal_Annotation (Arg3_Exp, Prag);

      elsif Name = "might_not_return" then
         Check_Might_Not_Return_Annotation (Arg3_Exp, Prag);

      elsif Name = "no_wrap_around" then
         Check_No_Wrap_Around_Annotation (Arg3_Exp);

      elsif Name in "always_return" | "terminating" then
         if Name = "terminating" then
            Error_Msg_N
              (Warning_Message (Warn_Pragma_Annotate_Terminating), Prag);
            Error_Msg_N ("\\use Always_Return instead", Prag);
         end if;

         Check_Always_Return_Annotation (Arg3_Exp, Prag);

      --  Annotations with 4 arguments

      elsif Name = "ownership" then
         Check_Ownership_Annotation (Aspect_Or_Pragma, Arg3_Exp, Arg4_Exp);

      elsif Name = "iterable_for_proof" then
         Check_Iterable_Annotation (Arg3_Exp, Arg4_Exp, Prag);

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

            if Nkind (Arg3_Exp) in N_String_Literal | N_Operator_Symbol
            then
               Pattern := Strval (Arg3_Exp);
            else
               Error_Msg_N
                 ("third argument PATTERN for 'G'N'A'Tprove Annotate "
                  & Aspect_Or_Pragma & " must be a string literal",
                  Prag);
               return;
            end if;

            if Nkind (Arg4_Exp) = N_String_Literal then
               Reason := Strval (Arg4_Exp);
            else
               Error_Msg_N
                 ("fourth argument REASON for 'G'N'A'Tprove Annotate "
                  & Aspect_Or_Pragma & " must be a string literal",
                  Prag);
               return;
            end if;

            Result := Check_Justification'(Present => True,
                                           Kind    => Kind,
                                           Pattern => Pattern,
                                           Reason  => Reason);
         end;
      end if;
   end Check_Pragma_Annotate_GNATprove;

   ---------------------------------------
   -- Set_Has_No_Wrap_Around_Annotation --
   ---------------------------------------

   procedure Set_Has_No_Wrap_Around_Annotation (E : Entity_Id) is
   begin
      No_Wrap_Around_Annotations.Include (Unique_Entity (E));
   end Set_Has_No_Wrap_Around_Annotation;

end SPARK_Definition.Annotate;
