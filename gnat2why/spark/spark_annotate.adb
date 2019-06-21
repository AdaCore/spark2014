------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        S P A R K _ A N N O T A T E                       --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2011-2019, AdaCore                     --
--                Copyright (C) 2014-2019, Altran UK Limited                --
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
with Ada.Containers.Doubly_Linked_Lists;
with Aspects;                      use Aspects;
with Common_Containers;
with Errout;                       use Errout;
with GNAT.Regpat;                  use GNAT.Regpat;
with Namet;                        use Namet;
with Nlists;                       use Nlists;
with Sem_Aux;                      use Sem_Aux;
with Sem_Util;                     use Sem_Util;
with Sinfo;                        use Sinfo;
with Sinput;                       use Sinput;
with Snames;                       use Snames;
--  ??? "use"ing SPARK_Definition would lead to a name resolution error
with SPARK_Definition;
with SPARK_Util.Subprograms;       use SPARK_Util.Subprograms;
with SPARK_Util.Types;             use SPARK_Util.Types;
with Stringt;                      use Stringt;

package body SPARK_Annotate is

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

   Inline_Annotations : Common_Containers.Node_Maps.Map :=
     Common_Containers.Node_Maps.Empty_Map;
   --  Maps all the function entities E with a pragma Annotate
   --  (GNATprove, Inline_For_Proof, E) to their expression.
   Inline_Pramas : Common_Containers.Node_Maps.Map :=
     Common_Containers.Node_Maps.Empty_Map;
   --  Maps all the function entities E with a pragma Annotate
   --  (GNATprove, Inline_For_Proof, E) to th pragma. This is used to get
   --  better location for checks for inline.

   Iterable_Annotations : Iterable_Maps.Map := Iterable_Maps.Empty_Map;
   --  A map from Iterable aspects to Iterable annotations

   Terminate_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores subprogram and package entities with a pragma Annotate
   --  (GNATprove, Terminating, E).

   Init_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores type entities with a pragma Annotate
   --  (GNATprove, Init_By_Proof, E).

   Pledge_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores type entities with a pragma Annotate (GNATprove, Pledge, E).

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
      List            : List_Id);
   --  Same as above, but compute the node range from a list of nodes

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

   procedure Syntax_Check_Pragma_Annotate_Gnatprove
     (Node    : Node_Id;
      Ok      : out Boolean;
      Kind    : out Annotate_Kind;
      Pattern : out String_Id;
      Reason  : out String_Id);
   --  Check validity of the pragma Annotate (Gnatprove, ...), and fill in the
   --  kind, pattern and reason of the pragma. The boolean Ok is always set,
   --  the others are only set if Ok is True. Ok is False if some syntax error
   --  has been detected, or if the pragma Annotate is not used for
   --  justification purposes (it has Iterable_For_Proof or
   --  External_Axiomatization as a second argument). If it is necessary,
   --  Syntax_Check_Pragma_Annotate_Gnatprove reports this error.

   procedure Check_Inline_Annotation (Arg3_Exp : Node_Id; Prag : Node_Id);
   --  Check validity of a pragma Annotate (Gnatprove, Inline_For_Proof, )
   --  and insert it in the Inline_Annotations map.

   procedure Check_Iterable_Annotation
     (Arg3_Exp : Node_Id;
      Arg4_Exp : Node_Id);
   --  Check validity of a pragma Annotate (Gnatprove, Iterate_For_Proof, )
   --  and insert it in the Iterable_Annotations map.

   procedure Check_Terminate_Annotation (Arg3_Exp : Node_Id) with
     Pre => Present (Arg3_Exp);
   --  Check validity of a pragma Annotate (Gnatprove, Terminating, ) and
   --  insert it in the Terminate_Annotations map.

   procedure Check_Init_Annotation (Arg3_Exp : Node_Id) with
     Pre => Present (Arg3_Exp);
   --  Check validity of a pragma Annotate (Gnatprove, Init_By_Proof, E) and
   --  insert it in the Init_Annotations map.

   procedure Check_Pledge_Annotation (Arg3_Exp : Node_Id) with
     Pre => Present (Arg3_Exp);
   --  Check validity of a pragma Annotate (Gnatprove, Pledge, E) and insert it
   --  in the Pledge_Annotations map.

   ---------
   -- "<" --
   ---------

   function "<" (L, R : Annotated_Range) return Boolean is
   begin
      return L.First < R.First;
   end "<";

   ---------------------------
   -- Check_Init_Annotation --
   ---------------------------

   procedure Check_Init_Annotation (Arg3_Exp : Node_Id) is
      E : constant Entity_Id := Entity (Arg3_Exp);

   begin
      --  This entity must be a scalar type

      if not Is_Scalar_Type (E) then
         Error_Msg_N
           ("Entity parameter of a pragma Init_By_Proof must be a scalar "
            & "type",
            Arg3_Exp);
         return;
      elsif Has_Predicates (E) then
         Error_Msg_N
           ("Entity parameter of a pragma Init_By_Proof must not have type "
            & "predicates",
            Arg3_Exp);
         return;
      end if;

      --  Go through renamings to find the appropriate entity

      Init_Annotations.Include (Unique_Entity (E));
   end Check_Init_Annotation;

   -----------------------------
   -- Check_Inline_Annotation --
   -----------------------------

   procedure Check_Inline_Annotation (Arg3_Exp : Node_Id; Prag : Node_Id) is
      E     : Entity_Id;
      Nodes : Common_Containers.Node_Lists.List;
      Value : Node_Id;

      use type Ada.Containers.Count_Type;

   begin
      --  The third argument must be an entity

      pragma Assert (Present (Arg3_Exp) and then Present (Entity (Arg3_Exp)));
      E := Entity (Arg3_Exp);

      --  This entity must be a function

      if Ekind (E) /= E_Function then
         Error_Msg_N
           ("Entity parameter of a pragma Inline_For_Proof must be a function",
            Arg3_Exp);
         return;
      end if;

      if Present (Get_Expression_Function (E))
        and then SPARK_Definition.Entity_Body_Compatible_With_SPARK (E)
      then
         Value := Expression (Get_Expression_Function (E));
      else

         --  It must have a postcondition

         Nodes := Find_Contracts (E, Pragma_Postcondition, False, False);

         if Nodes.Length /= 1 then
            Error_Msg_N
              ("function with Inline_For_Proof must be an expression function"
               & " or have a postcondition of the form F'Result = Expr", E);
            return;
         end if;

         --  Its postcondition must be of the form F'Result = Expr

         Value := Nodes.First_Element;

         if Nkind (Value) = N_Op_Eq
           and then Nkind (Left_Opnd (Value)) = N_Attribute_Reference
           and then Get_Attribute_Id (Attribute_Name (Left_Opnd (Value))) =
           Attribute_Result
         then
            Value := Right_Opnd (Value);
         elsif Nkind (Value) = N_Function_Call
           and then Nkind (Original_Node (Value)) = N_Op_Eq
           and then Nkind (Left_Opnd (Original_Node (Value))) =
           N_Attribute_Reference
           and then Get_Attribute_Id
             (Attribute_Name (Left_Opnd (Original_Node (Value)))) =
           Attribute_Result
         then
            Value := Next_Actual (First_Actual (Value));
         else
            Error_Msg_N
              ("function with Inline_For_Proof must be an expression function"
               & " or have a postcondition of the form F'Result = Expr", E);
            return;
         end if;
      end if;

      Inline_Annotations.Include (E, Value);
      Inline_Pramas.Include (E, Prag);
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
           and then Match (String_Value (E.Pattern), Msg)
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
      Arg4_Exp : Node_Id)
   is

      procedure Check_Contains_Entity (E : Entity_Id; Ok : in out Boolean);
      --  Checks that E is a valid Contains function for a type with an
      --  Iterable aspect.

      procedure Check_Model_Entity (E : Entity_Id; Ok : in out Boolean);
      --  Checks that E is a valid Model function for a type with an
      --  Iterable aspect.

      procedure Process_Iterable_Annotation
        (Kind   : Iterable_Kind;
         Entity : Entity_Id);
      --  Insert an iterable annotation into the Iterable_Annotations map and
      --  mark the iterable functions.

      ---------------------------
      -- Check_Contains_Entity --
      ---------------------------

      procedure Check_Contains_Entity (E : Entity_Id; Ok : in out Boolean) is
         Params  : constant List_Id :=
                    Parameter_Specifications (Subprogram_Specification (E));
         C_Param : constant Node_Id := First (Params);
      begin
         if No (C_Param)
           or else No (Next (C_Param))
           or else Present (Next (Next (C_Param)))
         then
            Error_Msg_N
              ("Contains function must have exactly two parameters", E);
         elsif not Is_Standard_Boolean_Type (Etype (E)) then
            Error_Msg_N
              ("Contains function must return Booleans", E);
         else
            declare
               E_Param        : constant Node_Id := Next (C_Param);
               Container_Type : constant Entity_Id :=
                 Entity (Parameter_Type (C_Param));
               --  Type of the first Argument of the Contains function

               Element_Type   : constant Entity_Id :=
                 Entity (Parameter_Type (E_Param));
               --  Type of the second argument of the Contains function

               Cont_Element   : constant Entity_Id :=
                 SPARK_Util.Types.Get_Iterable_Type_Primitive
                   (Container_Type, Name_Element);
               --  Element primitive of Container_Type
            begin
               if No (Cont_Element) then
                  Error_Msg_N
                    ("first parameter of Contains function must allow for of "
                     & "iteration", C_Param);
               elsif Etype (Cont_Element) /= Element_Type then
                  Error_Msg_N
                    ("second parameter of Contains must have the type of "
                     & "elements", E_Param);
               else
                  Ok := True;
               end if;
            end;
         end if;
      end Check_Contains_Entity;

      ------------------------
      -- Check_Model_Entity --
      ------------------------

      procedure Check_Model_Entity (E : Entity_Id; Ok : in out Boolean) is
         Params : constant List_Id :=
           Parameter_Specifications (Subprogram_Specification (E));
         Param  : constant Node_Id := First (Params);
      begin
         if No (Param) or else Present (Next (Param)) then
            Error_Msg_N
              ("Model function must have exactly one parameter", E);
         else
            declare
               Container_Type : constant Entity_Id :=
                 Entity (Parameter_Type (Param));
               --  Type of the first Argument of the model function

               Model_Type     : constant Entity_Id := Etype (E);
               --  Return type of the model function

               Cont_Element   : constant Entity_Id :=
                 SPARK_Util.Types.Get_Iterable_Type_Primitive
                   (Container_Type, Name_Element);
               --  Element primitive of Container_Type

               Model_Element  : constant Entity_Id :=
                 SPARK_Util.Types.Get_Iterable_Type_Primitive
                   (Model_Type, Name_Element);
               --  Element primitive of Model_Type
            begin
               if No (Cont_Element) then
                  Error_Msg_N
                    ("parameter of Model function must allow for of iteration",
                     Param);
               elsif No (Model_Element) then
                  Error_Msg_N
                    ("return type of Model function must allow for of " &
                       "iteration", E);
               else
                  Ok := True;
               end if;
            end;
         end if;
      end Check_Model_Entity;

      ---------------------------------
      -- Process_Iterable_Annotation --
      ---------------------------------

      procedure Process_Iterable_Annotation
        (Kind   : Iterable_Kind;
         Entity : Entity_Id)
      is
         Container_Type : constant Entity_Id := Etype (First_Entity (Entity));
         Iterable_Node  : constant Node_Id :=
           Find_Value_Of_Aspect (Container_Type, Aspect_Iterable);
         Model_Iterable_Aspect : constant Node_Id :=
           Find_Aspect (Etype (Entity), Aspect_Iterable);
      begin
         pragma Assert (Present (Iterable_Node));

         Iterable_Annotations.Insert
           (Iterable_Node, Iterable_Annotation'(Kind, Entity));
         if Present (Model_Iterable_Aspect) then
            SPARK_Definition.Mark_Iterable_Aspect (Model_Iterable_Aspect);
         end if;
      end Process_Iterable_Annotation;

      Args_Str : constant String_Id := Strval (Arg3_Exp);
      Kind     : Iterable_Kind;
      New_Prim : Entity_Id;
      Ok       : Boolean := False;

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
      end if;

      String_To_Name_Buffer (Args_Str);
      if Name_Len = 5 and then Name_Buffer (1 .. 5) = "Model" then
         Kind := Model;
         Check_Model_Entity (New_Prim, Ok);
      elsif Name_Len = 8 and then Name_Buffer (1 .. 8) = "Contains" then
         Kind := Contains;
         Check_Contains_Entity (New_Prim, Ok);
      else
         Error_Msg_N
           ("the third argument of a Gnatprove Annotate Iterable_For_Proof "
            & "pragma must be Model or Contains",
            Arg3_Exp);
         return;
      end if;

      if Ok then
         Process_Iterable_Annotation (Kind, New_Prim);
      end if;
   end Check_Iterable_Annotation;

   -----------------------------
   -- Check_Pledge_Annotation --
   -----------------------------

   procedure Check_Pledge_Annotation (Arg3_Exp : Node_Id) is

      procedure Check_Pledge_Entity (E : Entity_Id);

      -------------------------
      -- Check_Pledge_Entity --
      -------------------------

      procedure Check_Pledge_Entity (E : Entity_Id) is
         Borrower : constant Entity_Id := First_Formal (E);
      begin
         if No (Borrower)
           or else No (Next_Formal (Borrower))
           or else Present (Next_Formal (Next_Formal (Borrower)))
         then
            Error_Msg_N
              ("Pledge function must have exactly two parameters", E);
         elsif not Is_Ghost_Entity (E) then
            Error_Msg_N
              ("Pledge function must be a ghost function", E);
         elsif not Is_Standard_Boolean_Type (Etype (E)) then
            Error_Msg_N
              ("Pledge function must return Boolean", E);
         elsif No (Get_Expression_Function (E)) then
            Error_Msg_N
              ("Pledge function must be an expression function", E);
         else
            declare
               Pledge_Expr : constant Entity_Id := Next_Formal (Borrower);
            begin
               if not Is_Anonymous_Access_Type (Etype (Borrower)) then
                  Error_Msg_N
                    ("first parameter of Pledge function must be an anonymous "
                     & "access type", Borrower);
               elsif not Is_Standard_Boolean_Type (Etype (Pledge_Expr)) then
                  Error_Msg_N
                    ("second parameter of Pledge function must be a Boolean",
                     Pledge_Expr);
               else
                  declare
                     Expr : constant Node_Id :=
                       Expression (Get_Expression_Function (E));
                  begin
                     if Nkind (Expr) not in N_Expanded_Name | N_Identifier
                       or else Entity (Expr) /= Pledge_Expr
                     then
                        Error_Msg_N
                          ("expression of a Pledge function must be its second"
                           & " parameter", Pledge_Expr);
                     end if;
                  end;
               end if;
            end;
         end if;
      end Check_Pledge_Entity;

      E : Entity_Id;
   begin
      if Nkind (Arg3_Exp) not in N_Has_Entity then
         Error_Msg_N
           ("third parameter of a pragma Pledge must be an entity",
            Arg3_Exp);
      else
         E := Entity (Arg3_Exp);
      end if;

      --  This entity must be a function

      if Ekind (E) /= E_Function then
         Error_Msg_N
           ("entity parameter of a pragma Pledge must be a function",
            Arg3_Exp);
         return;
      else
         Check_Pledge_Entity (E);
      end if;

      --  Go through renamings to find the appropriate entity

      Pledge_Annotations.Include (Unique_Entity (E));
   end Check_Pledge_Annotation;

   --------------------------------
   -- Check_Terminate_Annotation --
   --------------------------------

   procedure Check_Terminate_Annotation (Arg3_Exp : Node_Id) is
      E : constant Entity_Id := Entity (Arg3_Exp);

   begin
      --  The third argument must be an entity

      pragma Assert (Present (E));

      --  This entity must be a function

      if Ekind (E) not in
        Subprogram_Kind | E_Package | Generic_Subprogram_Kind
      then
         Error_Msg_N
           ("Entity parameter of a pragma Terminating must be a subprogram or "
            & "a package",
            Arg3_Exp);
         return;
      end if;

      --  Go through renamings to find the appropriate entity

      Terminate_Annotations.Include (Get_Renamed_Entity (E));
   end Check_Terminate_Annotation;

   ------------------------
   -- Find_Inline_Pragma --
   ------------------------

   function Find_Inline_Pragma (E : Entity_Id) return Node_Id is
     (Inline_Pramas.Element (E));

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
            Error_Msg_N ("?no check message justified by this pragma", Prag);
         end if;
      end loop;

      for Prag of Proved_Pragma loop
         if Instantiation_Location (Sloc (Prag)) = No_Location then
            Error_Msg_N
              ("?only proved check messages justified by this pragma",
               Prag);
         end if;
      end loop;
   end Generate_Useless_Pragma_Annotate_Warnings;

   ---------------------------
   -- Has_Pledge_Annotation --
   ---------------------------

   function Has_Pledge_Annotation (E : Entity_Id) return Boolean is
     (Pledge_Annotations.Contains (E));

   ------------------------------
   -- Has_Terminate_Annotation --
   ------------------------------

   function Has_Terminate_Annotation (E : Entity_Id) return Boolean is
      Unit : constant Entity_Id :=
        (if Present (Scope (E)) then Enclosing_Unit (E) else Empty);
   begin
      return Terminate_Annotations.Contains (E)
        or else (Present (Unit)
                 and then Ekind (Unit) = E_Package
                 and then Has_Terminate_Annotation (Unit));
   end Has_Terminate_Annotation;

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

      --  The following if-block achieves two things:
      --  - it avoids a call to Sloc_Range with a N_Subprogram_Body node, which
      --    doesn't work;
      --  - includes the spec node in the range to be considered for subprogram
      --    bodies.

      if Nkind (Range_Node) = N_Subprogram_Body
        and then Present (Corresponding_Spec (Range_Node))
      then
         Insert_Annotate_Range (Prgma, Kind, Pattern, Reason,
                                Specification (Range_Node), Whole => True);
         Insert_Annotate_Range (Prgma, Kind, Pattern, Reason,
                                Handled_Statement_Sequence (Range_Node),
                                Whole => True);
         Insert_Annotate_Range (Prgma, Kind, Pattern, Reason,
                                Declarations (Range_Node));
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

      Cur : Cursor := Annotations.First;
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

   procedure Insert_Annotate_Range
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      List            : List_Id)
   is
      First_Sloc, Last_Sloc, Tmp : Source_Ptr;
   begin
      if No (List) then
         return;
      end if;
      Sloc_Range (First (List), First_Sloc, Tmp);
      Sloc_Range (Last (List), Tmp, Last_Sloc);
      Insert_Annotate_Range
        (Prgma, Kind, Pattern, Reason, First_Sloc, Last_Sloc);
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
      Ok              : Boolean;
      Pattern, Reason : String_Id;
      Kind            : Annotate_Kind;

   begin
      if Pragma_Seen.Contains (N) then
         return;
      else
         Pragma_Seen.Insert (N);
      end if;
      Syntax_Check_Pragma_Annotate_Gnatprove (N, Ok, Kind, Pattern, Reason);

      if not Ok then
         return;
      end if;

      if Consider_Next then
         Insert_With_Next (N, Kind, Pattern, Reason, Preceding);
      else
         Insert_Annotate_Range (N, Kind, Pattern, Reason, Preceding,
                                Whole => False);
      end if;
   end Mark_Pragma_Annotate;

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

   ------------------------------
   -- Scalar_Has_Init_By_Proof --
   ------------------------------

   function Scalar_Has_Init_By_Proof (E : Entity_Id) return Boolean is
     (Is_Scalar_Type (E)
      and then Init_Annotations.Contains (Unique_Entity (E)));

   --------------------------------------------
   -- Syntax_Check_Pragma_Annotate_Gnatprove --
   --------------------------------------------

   procedure Syntax_Check_Pragma_Annotate_Gnatprove
     (Node     : Node_Id;
      Ok       : out Boolean;
      Kind     : out Annotate_Kind;
      Pattern  : out String_Id;
      Reason   : out String_Id)
   is
      pragma Annotate (CodePeer, Intentional,
                       "validity check",
                       "other out parameters only set when Ok is True");

      Arg1, Arg2, Arg3, Arg4 : Node_Id;
      Arg2_Exp, Arg3_Exp, Arg4_Exp : Node_Id;

      Number_Of_Pragma_Args : constant Nat :=
        List_Length (Pragma_Argument_Associations (Node));

   begin
      --  We silently ignore these cases

      if Number_Of_Pragma_Args = 2  then
         declare
            Arg1 : constant Node_Id :=
              First (Pragma_Argument_Associations (Node));
            Arg2 : constant Node_Id := Next (Arg1);
         begin
            if Get_Name_String (Chars (Get_Pragma_Arg (Arg2))) =
              "external_axiomatization"
            then
               Ok := False;
               return;
            end if;
         end;
      elsif Number_Of_Pragma_Args = 3  then
         Arg1 := First (Pragma_Argument_Associations (Node));
         Arg2 := Next (Arg1);
         Arg3 := Next (Arg2);
         Arg3_Exp := Expression (Arg3);
         if Get_Name_String (Chars (Get_Pragma_Arg (Arg2))) =
           "inline_for_proof"
         then
            Check_Inline_Annotation (Arg3_Exp, Node);
            Ok := False;
            return;
         elsif Get_Name_String (Chars (Get_Pragma_Arg (Arg2))) = "terminating"
         then
            Check_Terminate_Annotation (Arg3_Exp);
            Ok := False;
            return;
         elsif Get_Name_String (Chars (Get_Pragma_Arg (Arg2))) =
           "init_by_proof"
         then
            Check_Init_Annotation (Arg3_Exp);
            Ok := False;
            return;
         elsif Get_Name_String (Chars (Get_Pragma_Arg (Arg2))) = "pledge" then
            Check_Pledge_Annotation (Arg3_Exp);
            Ok := False;
            return;
         end if;
      end if;

      --  We set Ok to false so that whenever we detect a problem we can simply
      --  return. Only when all checks passed, we set Ok to True.

      Ok := False;

      --  in the case of an annotate aspect, there is a fifth argument
      --  for the entity to which the aspect applies. We check for this
      --  situation explicitly below, to avoid the error message in that
      --  case.

      if Number_Of_Pragma_Args not in 4 .. 5 then
         Error_Msg_N
           ("a Gnatprove Annotate pragma requires exactly 4 arguments",
            Node);
         return;
      end if;
      Arg1 := First (Pragma_Argument_Associations (Node));
      Arg2 := Next (Arg1);
      Arg3 := Next (Arg2);
      Arg4 := Next (Arg3);
      Arg2_Exp := Expression (Arg2);
      Arg3_Exp := Expression (Arg3);
      Arg4_Exp := Expression (Arg4);

      if Number_Of_Pragma_Args = 5 then
         declare
            Arg5 : constant Node_Id := Next (Arg4);
         begin
            if Chars (Arg5) = No_Name
              or else Get_Name_String (Chars (Arg5)) /= "entity"
            then
               Error_Msg_N
                 ("a Gnatprove Annotate pragma requires exactly 4 arguments",
                  Node);
            end if;
         end;
      end if;

      if Nkind (Arg2_Exp) = N_Identifier then
         declare
            Args_Str : constant String := Get_Name_String (Chars (Arg2_Exp));
         begin
            if Args_Str = "false_positive" then
               Kind := False_Positive;
            elsif Args_Str = "intentional" then
               Kind := Intentional;
            elsif Args_Str = "iterable_for_proof" then
               Check_Iterable_Annotation (Arg3_Exp, Arg4_Exp);
               return;
            else
               Error_Msg_N
                 ("the second argument of a Gnatprove Annotate pragma must " &
                    "be False_Positive or Intentional",
                  Node);
               return;
            end if;
         end;
      else
         Error_Msg_N
           ("the second argument of a Gnatprove Annotate pragma must " &
              "be False_Positive or Intentional",
            Node);
         return;
      end if;
      if Nkind (Arg3_Exp) = N_String_Literal then
         Pattern := Strval (Arg3_Exp);
      else
         Error_Msg_N
           ("the third argument of a Gnatprove Annotate pragma must " &
              "be a string literal",
            Node);
         return;
      end if;
      if Nkind (Arg4_Exp) = N_String_Literal then
         Reason := Strval (Arg4_Exp);
      else
         Error_Msg_N
           ("the fourth argument of a Gnatprove Annotate pragma must " &
              "be a string literal",
            Node);
         return;
      end if;
      Ok := True;
      return;
   end Syntax_Check_Pragma_Annotate_Gnatprove;

end SPARK_Annotate;
