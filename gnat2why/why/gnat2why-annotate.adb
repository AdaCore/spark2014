------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - A N N O T A T E                   --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2011-2016, AdaCore                     --
--                     Copyright (C) 2014-2016, Altran UK Limited           --
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
with Ada.Containers.Vectors;
with Ada.Strings.Unbounded;  use Ada.Strings.Unbounded;
with Aspects;                use Aspects;
with Common_Containers;
with Einfo;                  use Einfo;
with Errout;                 use Errout;
with Gnat2Why_Args;
with GNAT.Regpat;            use GNAT.Regpat;
with Namet;                  use Namet;
with Nlists;                 use Nlists;
with Sem_Util;               use Sem_Util;
with Sinfo;                  use Sinfo;
with Sinput;                 use Sinput;
with Snames;                 use Snames;
with Stringt;                use Stringt;

package body Gnat2Why.Annotate is

   package Annot_Range_Vectors is new Ada.Containers.Vectors
     (Index_Type   => Natural,
      Element_Type => Annotated_Range,
      "="          => "=");

   package Iterable_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Node_Id,
      Element_Type    => Iterable_Annotation,
      Hash            => Common_Containers.Node_Hash,
      Equivalent_Keys => "=");

   Pragma_Set : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  After marking, this set contains all pragma Annotate nodes. They are
   --  removed from the set one by one when messages which are covered by these
   --  pragmas are encountered. At the end, only pragmas which don't cover a
   --  message will be in this set.

   Proved_Pragma : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  This set contains all pragma Annotate Nodes which correspond only to a
   --  proved check.

   Annotations : Annot_Range_Vectors.Vector :=
     Annot_Range_Vectors.Empty_Vector;
   --  A sorted vector of ranges

   Iterable_Annotations : Iterable_Maps.Map := Iterable_Maps.Empty_Map;
   --  A map from Iterable aspects to Iterable annotations

   procedure Insert_Annotate_Range
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      Range_Node      : Node_Id);
   --  Insert the node range into the sorted vector of node ranges

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
      First_Node      : Node_Id);
   --  Same as above, but also consider all nodes "next" after First_Node,
   --  until (and excluding) a node which comes from source.

   procedure Syntax_Check_Pragma_Annotate_Gnatprove
     (Node     : Node_Id;
      Ok       : out Boolean;
      Kind     : out Annotate_Kind;
      Pattern  : out String_Id;
      Reason   : out String_Id);
   --  Check validity of the pragma Annotate (Gnatprove, ...), and fill in the
   --  kind, pattern and reason of the pragma. The boolean Ok is always set,
   --  the others are only set if Ok is True. Ok is False if some syntax error
   --  has been detected, or if the pragma Annotate is not used for
   --  justification purposes (it has Iterable_For_Proof or
   --  External_Axiomatization as a second argument). If it is necessary,
   --  Syntax_Check_Pragma_Annotate_Gnatprove reports this error.

   procedure Check_Iterable_Annotation
     (Arg3_Exp : Node_Id;
      Arg4_Exp : Node_Id);
   --  Check validity of a pragma Annotate (Gnatprove, Iterate_For_Proof, )
   --  and inserts it in the Iterable_Annotations map.

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
     (Arg3_Exp :     Node_Id;
      Arg4_Exp :     Node_Id)
   is

      procedure Check_Contains_Entity (E : Entity_Id; Ok : in out Boolean);
      --  Checks that E is a valid Contains function for a type with an
      --  Iterable aspect.

      procedure Check_Model_Entity (E : Entity_Id; Ok : in out Boolean);
      --  Checks that E is a valid Contains function for a type with an
      --  Iterable aspect.

      procedure Insert_Iterable_Annotation
        (Kind   : Iterable_Kind;
         Entity : Entity_Id);
      --  Insert an iterable annotation into the Iterable_Annotations map.

      ------------------------
      -- Check_Contains_Entity --
      ------------------------

      procedure Check_Contains_Entity (E : Entity_Id; Ok : in out Boolean) is
      begin
         if No (First_Entity (E))
           or else No (Next_Entity (First_Entity (E)))
           or else Present (Next_Entity (Next_Entity (First_Entity (E))))
         then
            Error_Msg_N
              ("Contains function must have exactly two parameter", E);
         elsif not Is_Standard_Boolean_Type (Etype (E)) then
            Error_Msg_N
              ("Contains function must return Booleans", E);
         else
            declare
               Container_Type : constant Entity_Id := Etype (First_Entity (E));
               --  Type of the first Argument of the Contains function

               Element_Type   : constant Entity_Id :=
                 Etype (Next_Entity (First_Entity (E)));
               --  Type of the second argument of the Contains function

               Cont_Element   : constant Entity_Id :=
                 Get_Iterable_Type_Primitive (Container_Type, Name_Element);
               --  Element primitive of Container_Type
            begin
               if No (Cont_Element) then
                  Error_Msg_N
                    ("first parameter of Contains function must allow for of "
                     & "iteration", First_Entity (E));
               elsif Etype (Cont_Element) /= Element_Type then
                  Error_Msg_N
                    ("second parameter of Contains must have the type of "
                     & "elements", Next_Entity (First_Entity (E)));
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
      begin
         if No (First_Entity (E))
           or else Present (Next_Entity (First_Entity (E)))
         then
            Error_Msg_N
              ("Model function must have exactly one parameter", E);
         else
            declare
               Container_Type : constant Entity_Id := Etype (First_Entity (E));
               --  Type of the first Argument of the model function

               Model_Type     : constant Entity_Id := Etype (E);
               --  Return type of the model function

               Cont_Element   : constant Entity_Id :=
                 Get_Iterable_Type_Primitive (Container_Type, Name_Element);
               --  Element primitive of Container_Type

               Model_Element  : constant Entity_Id :=
                 Get_Iterable_Type_Primitive (Model_Type, Name_Element);
               --  Element primitive of Model_Type
            begin
               if No (Cont_Element) then
                  Error_Msg_N
                    ("parameter of Model function must allow for of iteration",
                     First_Entity (E));
               elsif No (Model_Element) then
                  Error_Msg_N
                    ("return type of Model function must allow for of " &
                       "iteration", E);
               elsif Etype (Cont_Element) /= Etype (Model_Element) then
                  Error_Msg_N
                    ("iteration on model and container types must range on "
                     & "the same elements", E);
               else
                  Ok := True;
               end if;
            end;
         end if;
      end Check_Model_Entity;

      --------------------------------
      -- Insert_Iterable_Annotation --
      --------------------------------

      procedure Insert_Iterable_Annotation
        (Kind   : Iterable_Kind;
         Entity : Entity_Id)
      is
         Container_Type : constant Entity_Id := Etype (First_Entity (Entity));
         Iterable_Node  : constant Node_Id :=
           Find_Value_Of_Aspect (Container_Type, Aspect_Iterable);
      begin
         pragma Assert (Present (Iterable_Node));
         pragma Assert (not Iterable_Annotations.Contains (Iterable_Node));
         Iterable_Annotations.Include
           (Iterable_Node, Iterable_Annotation'(Kind, Entity));
      end Insert_Iterable_Annotation;

      Args_Str : constant String_Id := Strval (Arg3_Exp);
      Kind     : Iterable_Kind;
      New_Prim : Entity_Id;
      Ok       : Boolean := False;
   begin

      --  The fourth argument must be an entity.

      pragma Assert (Present (Arg4_Exp) and then Present (Entity (Arg4_Exp)));
      New_Prim := Entity (Arg4_Exp);

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
         Insert_Iterable_Annotation (Kind, New_Prim);
      end if;
   end Check_Iterable_Annotation;

   -----------------------------------------------
   -- Generate_Useless_Pragma_Annotate_Warnings --
   -----------------------------------------------

   procedure Generate_Useless_Pragma_Annotate_Warnings is
   begin

      --  If the analysis is requested for a specific subprogram/task, we do
      --  not issue this warning, because it's likely to be a false positive.

      if Gnat2Why_Args.Limit_Subp /= Null_Unbounded_String then
         return;
      end if;

      --  We do not issue any warnings on nodes which stem from inlining or
      --  instantiation.

      for Prag of Pragma_Set loop
         if Instantiation_Location (Sloc (Prag)) = No_Location then
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
   -- Insert_Annotate_Range --
   ---------------------------

   procedure Insert_Annotate_Range
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      Range_Node      : Node_Id)
   is
      First_Sloc, Last_Sloc : Source_Ptr;
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
                                Specification (Range_Node));
         Insert_Annotate_Range (Prgma, Kind, Pattern, Reason,
                                Handled_Statement_Sequence (Range_Node));
         Insert_Annotate_Range (Prgma, Kind, Pattern, Reason,
                                Declarations (Range_Node));
         Insert_With_Next (Prgma, Kind, Pattern, Reason,
                           Parent (Parent (Corresponding_Spec (Range_Node))));
         return;
      end if;
      Sloc_Range (Range_Node, First_Sloc, Last_Sloc);
      Insert_Annotate_Range
        (Prgma, Kind, Pattern, Reason, First_Sloc, Last_Sloc);
   end Insert_Annotate_Range;

   procedure Insert_Annotate_Range
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      First, Last     : Source_Ptr)
   is
      use Annot_Range_Vectors;

      Cur : Cursor := Annotations.First;
   begin
      Pragma_Set.Include (Prgma);
      while Has_Element (Cur) and then First > Annotations (Cur).First loop
         Next (Cur);
      end loop;
      Annotations.Insert
        (Cur,
         (Kind    => Kind,
          First   => First,
          Last    => Last,
          Pattern => Pattern,
          Reason  => Reason,
          Prgma   => Prgma));
   end Insert_Annotate_Range;

   procedure Insert_Annotate_Range
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      List            : List_Id)
   is
      First_Sloc, Last_Sloc, Tmp : Source_Ptr;
   begin
      if Present (List) then
         Sloc_Range (First (List), First_Sloc, Tmp);
         Sloc_Range (Last (List), Tmp, Last_Sloc);
      end if;
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
      First_Node      : Node_Id)
   is
      Node : Node_Id := First_Node;
   begin
      Insert_Annotate_Range (Prgma, Kind, Pattern, Reason, Node);
      Next (Node);
      while Present (Node) and not Comes_From_Source (Node) loop
         Insert_Annotate_Range (Prgma, Kind, Pattern, Reason, Node);
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
      Syntax_Check_Pragma_Annotate_Gnatprove (N, Ok, Kind, Pattern, Reason);

      if not Ok then
         return;
      end if;

      declare
         Decl : constant Node_Id := Enclosing_Declaration (Preceding);
         Ent  : constant Entity_Id := Unique_Defining_Entity (Decl);
      begin

         --  Also, if the requested subprogram is always inlined, and also
         --  referenced, the pragma should be ignored

         if Is_Local_Subprogram_Always_Inlined (Ent)
           and then Referenced (Ent)
         then
            return;
         end if;
      end;

      if Consider_Next then
         Insert_With_Next (N, Kind, Pattern, Reason, Preceding);
      else
         Insert_Annotate_Range (N, Kind, Pattern, Reason, Preceding);
      end if;
   end Mark_Pragma_Annotate;

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
         Info := Iterable_Maps.Element (C);
      end if;
   end Retrieve_Iterable_Annotation;

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
      Arg1, Arg2, Arg3, Arg4 : Node_Id;
      Arg2_Exp, Arg3_Exp, Arg4_Exp : Node_Id;

   begin
      --  We silently ignore this case

      if List_Length (Pragma_Argument_Associations (Node)) = 2  then
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
      end if;

      --  We set Ok to false so that whenever we detect a problem we can simply
      --  return. Only when all checks passed, we set Ok to True.

      Ok := False;

      if List_Length (Pragma_Argument_Associations (Node)) /= 4 then
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

end Gnat2Why.Annotate;
