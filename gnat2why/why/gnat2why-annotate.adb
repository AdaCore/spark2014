------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - A N N O T A T E                   --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2011-2015, AdaCore                     --
--                     Copyright (C) 2014-2015, Altran UK Limited           --
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

with AA_Util;              use AA_Util;
with Ada.Containers.Vectors;
with Common_Containers;
with Errout;               use Errout;
with GNAT.Regpat;          use GNAT.Regpat;
with Namet;                use Namet;
with Nlists;               use Nlists;
with Sinfo;                use Sinfo;
with Sinput;               use Sinput;

package body Gnat2Why.Annotate is

   package Annot_Range_Vectors is new Ada.Containers.Vectors
     (Index_Type   => Natural,
      Element_Type => Annotated_Range,
      "="          => "=");

   Pragma_Set : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  After marking, this set contains all pragma Annotate Nodes. They are
   --  removed from the set one by one when messages which are covered by these
   --  pragmas are encountered. At the end, only pragmas which don't cover a
   --  message will be in this set.

   Proved_Pragma : Common_Containers.Node_Sets.Set :=
     Common_Containers.Node_Sets.Empty_Set;
   --  This set contains all pragma Annotate Nodes which correspond only to a
   --  proved check.

   Annotations : Annot_Range_Vectors.Vector :=
     Annot_Range_Vectors.Empty_Vector;
   --  a sorted vector of ranges

   procedure Insert_Annotate_Range
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      Range_Node      : Node_Id);
   --  insert the node range into the sorted vector of node ranges

   procedure Insert_Annotate_Range
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      List            : List_Id);
   --  same as above, but compute the node range from a list of nodes

   procedure Insert_Annotate_Range
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      First, Last     : Source_Ptr);
   --  same as above, but take the node range in argument

   procedure Insert_With_Next
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      First_Node      : Node_Id);
   --  same as above, but also consider all nodes "next" after First_Node,
   --  until (and excluding) a node which comes from source

   procedure Syntax_Check_Pragma_Annotate_Gnatprove
     (Node     : Node_Id;
      Ok       : out Boolean;
      Kind     : out Annotate_Kind;
      Pattern  : out String_Id;
      Reason   : out String_Id);
   --  check validity of the pragma Annotate (Gnatprove, ...), and fill in the
   --  kind, pattern and reason of the pragma. The boolean Ok is always set,
   --  the others are only set if Ok is True. Ok is False if some syntax error
   --  has been detected, and Check_Pragma_Annotate_Gnatprove reports this
   --  error.

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

      --  this is a simple linear search in a sorted list, the only subtle
      --  thing is that several entries may match, or entries may include
      --  other entries.

      for E : Annotated_Range of Annotations loop

         --  if the current annotation_range starts already after the one we
         --  look for, then we can stop

         if Node_Slc < E.First then
            return;

         --  this is the case where the ranges match, but we have to check
         --  whether the pattern matches, too

         elsif Node_Slc <= E.Last
           and then Match (String_Value (E.Pattern), Msg)
         then
            Info := E;
            Found := True;

            --  deal with useless pragma Annotate
            --  Check = False means a proved message

            if not Check then

               --  if this is the first check which corresponds to this pragma,
               --  it possibly only corresponds to proved checks

               if Pragma_Set.Contains (Info.Prgma) then
                  Proved_Pragma.Include (Info.Prgma);
               end if;

            --  Check = True means a check message

            else

               --  a real check means the pragma is useful

               Proved_Pragma.Exclude (Info.Prgma);
            end if;

            --  in all cases we have now encountered this pragma and can remove
            --  it from pragma set

            Pragma_Set.Exclude (Info.Prgma);
            return;

         --  there is nothing to do in this case, but there may be other ranges
         --  later which may still be interesting.

         else
            null;
         end if;
      end loop;
   end Check_Is_Annotated;

   -----------------------------------------------
   -- Generate_Useless_Pragma_Annotate_Warnings --
   -----------------------------------------------

   procedure Generate_Useless_Pragma_Annotate_Warnings is
   begin
      for Prag of Pragma_Set loop
         Error_Msg_N ("?no check message justified by this pragma", Prag);
      end loop;
      for Prag of Proved_Pragma loop
         Error_Msg_N ("?only proved check messages justified by this pragma",
                      Prag);
      end loop;
   end Generate_Useless_Pragma_Annotate_Warnings;

   ---------------------------
   -- Insert_Annotate_Range --
   ---------------------------

   procedure Insert_Annotate_Range
     (Prgma           : Node_Id;
      Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      Range_Node      : Node_Id) is

      First_Sloc, Last_Sloc : Source_Ptr;
   begin

      if No (Range_Node) then
         return;
      end if;

      --  The following if-block achieves two things:
      --  - it avoids a call to Sloc_Range with a N_Subprogram_Body node, which
      --    doesn't work;
      --  - includes the spec node in the range to be considered for subprogram
      --  bodies

      if Nkind (Range_Node) = N_Subprogram_Body then
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
      while Has_Element (Cur) and then First > Element (Cur).First loop
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
      if Consider_Next then
         Insert_With_Next (N, Kind, Pattern, Reason, Preceding);
      else
         Insert_Annotate_Range (N, Kind, Pattern, Reason, Preceding);
      end if;
   end Mark_Pragma_Annotate;

   --------------------------------------------
   -- Syntax_Check_Pragma_Annotate_Gnatprove --
   --------------------------------------------

   procedure Syntax_Check_Pragma_Annotate_Gnatprove
     (Node     : Node_Id;
      Ok       : out Boolean;
      Kind     : out Annotate_Kind;
      Pattern  : out String_Id;
      Reason   : out String_Id) is
      Arg1, Arg2, Arg3, Arg4 : Node_Id;
      Arg2_Exp, Arg3_Exp, Arg4_Exp : Node_Id;
   begin

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

            --  we can silently ignore this case

            elsif Args_Str = "external_axiomatization" then
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
