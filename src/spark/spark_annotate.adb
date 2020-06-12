------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                        S P A R K _ A N N O T A T E                       --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2011-2020, AdaCore                     --
--                Copyright (C) 2014-2020, Altran UK Limited                --
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
with String_Utils;                 use String_Utils;

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
   Inline_Pragmas : Common_Containers.Node_Maps.Map :=
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

   Might_Not_Return_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores procedure entities with a pragma Annotate
   --  (GNATprove, Might_Not_Return, E).

   No_Wrap_Around_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores type entities with a pragma Annotate
   --  (GNATprove, No_Wrap_Around, E).

   Pledge_Annotations : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  Stores function entities with a pragma Annotate (GNATprove, Pledge, E).

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

   procedure Check_Init_Annotation (Arg3_Exp : Node_Id) with
     Pre => Present (Arg3_Exp);
   --  Check validity of a pragma Annotate (Gnatprove, Init_By_Proof, E) and
   --  insert it in the Init_Annotations map.

   procedure Check_Inline_Annotation (Arg3_Exp : Node_Id; Prag : Node_Id);
   --  Check validity of a pragma Annotate (Gnatprove, Inline_For_Proof, E)
   --  and insert it in the Inline_Annotations map.

   procedure Check_Iterable_Annotation
     (Arg3_Exp : Node_Id;
      Arg4_Exp : Node_Id);
   --  Check validity of a pragma Annotate (Gnatprove, Iterate_For_Proof, E)
   --  and insert it in the Iterable_Annotations map.

   procedure Check_Might_Not_Return_Annotation
     (Arg3_Exp : Node_Id;
      Prag     : Node_Id);
   --  Check validity of a pragma Annotate (Gnatprove, Might_Not_Return, E)
   --  and insert it in the Might_Not_Return_Annotations map.

   procedure Check_No_Wrap_Around_Annotation (Arg3_Exp : Node_Id);
   --  Check validity of a pragma Annotate (GNATprove, No_Wrap_Around, E)
   --  and insert it in the No_Wrap_Around_Annotations map.

   procedure Check_Pledge_Annotation (Arg3_Exp : Node_Id) with
     Pre => Present (Arg3_Exp);
   --  Check validity of a pragma Annotate (Gnatprove, Pledge, E) and insert it
   --  in the Pledge_Annotations map.

   procedure Check_Terminate_Annotation
     (Arg3_Exp : Node_Id;
      Prag     : Node_Id)
   with Pre => Present (Arg3_Exp);
   --  Check validity of a pragma Annotate (Gnatprove, Terminating, E) and
   --  insert it in the Terminate_Annotations map.

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
      if not Is_Type (E) then
         Error_Msg_N
           ("Entity parameter of a pragma Init_By_Proof must be a type",
            Arg3_Exp);
         return;
      elsif not Is_Base_Type (E) and then not Is_First_Subtype (E) then
         Error_Msg_N
           ("Pragma Init_By_Proof cannot be applied on a subtype",
            Arg3_Exp);
         return;
      end if;

      if SPARK_Definition.Entity_In_SPARK (E) then
         SPARK_Definition.Mark_Type_With_Relaxed_Init (E, E, True);
      end if;
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

      --  This entity must be a procedure

      if Ekind (E) /= E_Procedure then
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
         return;

      --  The procedure should not be annotated as terminating

      elsif Has_Terminate_Annotation (E) then
         Error_Msg_N
           ("procedure with " & Aspect_Or_Pragma & " Annotate "
            & "Might_Not_Return must not also be marked with Terminating",
            Arg3_Exp);
         return;

      --  The procedure should not be dispatching

      elsif Is_Dispatching_Operation (E) then
         Error_Msg_N
           ("procedure with " & Aspect_Or_Pragma & " Annotate "
            & "Might_Not_Return must not also be dispatching",
            Arg3_Exp);
         return;
      end if;

      Might_Not_Return_Annotations.Include (E);
   end Check_Might_Not_Return_Annotation;

   -------------------------------------
   -- Check_No_Wrap_Around_Annotation --
   -------------------------------------

   procedure Check_No_Wrap_Around_Annotation (Arg3_Exp : Node_Id) is
      E    : constant Entity_Id := Entity (Arg3_Exp);
      Decl : constant Node_Id := Parent (E);
      Base : Entity_Id;

   begin
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
         return;
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
      --  ??? this comment only applies to Check_Terminate_Annotation, where
      --  Get_Renamed_Entity is called. What about others?

      Pledge_Annotations.Include (Unique_Entity (E));
   end Check_Pledge_Annotation;

   --------------------------------
   -- Check_Terminate_Annotation --
   --------------------------------

   procedure Check_Terminate_Annotation
     (Arg3_Exp : Node_Id;
      Prag     : Node_Id)
   is
      From_Aspect      : constant Boolean := From_Aspect_Specification (Prag);
      Aspect_Or_Pragma : constant String :=
        (if From_Aspect then "aspect" else "pragma");
      E : constant Entity_Id := Entity (Arg3_Exp);

   begin
      --  The third argument must be an entity

      pragma Assert (Present (E));

      --  This entity must be a subprogram or a package

      if Ekind (E) not in
        Subprogram_Kind | E_Package | Generic_Subprogram_Kind
      then
         Error_Msg_N
           ("Entity parameter of a pragma Terminating must be a subprogram or "
            & "a package",
            Arg3_Exp);
         return;

      --  It must not be a procedure with No_Return

      elsif No_Return (E) then
         Error_Msg_N
           ("procedure with " & Aspect_Or_Pragma & " Annotate "
            & "Terminating must not also be marked with No_Return",
            Arg3_Exp);

      --  It must not be a procedure with Might_Not_Return

      elsif Ekind (E) = E_Procedure
        and then Has_Might_Not_Return_Annotation (E)
      then
         Error_Msg_N
           ("procedure with " & Aspect_Or_Pragma & " Annotate "
            & "Terminating must not also be marked with Might_Not_Return",
            Arg3_Exp);
      end if;

      --  Go through renamings to find the appropriate entity

      Terminate_Annotations.Include (Get_Renamed_Entity (E));
   end Check_Terminate_Annotation;

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

   -------------------------------------
   -- Has_Might_Not_Return_Annotation --
   -------------------------------------

   function Has_Might_Not_Return_Annotation (E : Entity_Id) return Boolean is
     (Ekind (E) = E_Procedure
      and then Might_Not_Return_Annotations.Contains (E));

   -----------------------------------
   -- Has_No_Wrap_Around_Annotation --
   -----------------------------------

   function Has_No_Wrap_Around_Annotation (E : Entity_Id) return Boolean is
     (No_Wrap_Around_Annotations.Contains (E));

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
               & " for 'G'N'A'Tprove", Arg);
            return "";

         elsif Nkind (Get_Pragma_Arg (Arg)) = N_Identifier then
            return Get_Name_String (Chars (Get_Pragma_Arg (Arg)));

         else
            Error_Msg_N
              ("expected name in Annotate " & Aspect_Or_Pragma
               & " for 'G'N'A'Tprove", Arg);
            return "";
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
         Check_Argument_Number (Name, 2, Ok);

      elsif Name = "init_by_proof"
        or else Name = "inline_for_proof"
        or else Name = "might_not_return"
        or else Name = "no_wrap_around"
        or else Name = "pledge"
        or else Name = "terminating"
      then
         Check_Argument_Number (Name, 3, Ok);

      elsif Name = "iterable_for_proof"
        or else (not From_Aspect
                 and then (Name = "false_positive"
                           or else Name = "intentional"))
      then
         Check_Argument_Number (Name, 4, Ok);

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

      --  Annotations with 2 arguments

      if Name = "external_axiomatization" then
         null;

      --  Annotations with 3 arguments

      elsif Name = "init_by_proof" then
         Check_Init_Annotation (Arg3_Exp);

      elsif Name = "inline_for_proof" then
         Check_Inline_Annotation (Arg3_Exp, Prag);

      elsif Name = "might_not_return" then
         Check_Might_Not_Return_Annotation (Arg3_Exp, Prag);

      elsif Name = "no_wrap_around" then
         Check_No_Wrap_Around_Annotation (Arg3_Exp);

      elsif Name = "pledge" then
         Check_Pledge_Annotation (Arg3_Exp);

      elsif Name = "terminating" then
         Check_Terminate_Annotation (Arg3_Exp, Prag);

      --  Annotations with 4 arguments

      elsif Name = "iterable_for_proof" then
         Check_Iterable_Annotation (Arg3_Exp, Arg4_Exp);

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

            if Nkind (Arg3_Exp) = N_String_Literal then
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

end SPARK_Annotate;
