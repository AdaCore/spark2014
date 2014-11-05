------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - A N N O T A T E                   --
--                                                                          --
--                                  B o d y                                 --
--                                                                          --
--                     Copyright (C) 2011-2014, AdaCore                     --
--                     Copyright (C) 2014, Altran UK Limited                --
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

   Annotations : Annot_Range_Vectors.Vector :=
     Annot_Range_Vectors.Empty_Vector;
   --  a sorted vector of ranges

   procedure Insert_Annotate_Range
     (Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      Range_Node      : Node_Id);
   --  insert the node range into the sorted vector of node ranges

   procedure Insert_Annotate_Range
     (Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      List            : List_Id);
   --  same as above, but compute the node range from a list of nodes

   procedure Insert_Annotate_Range
     (Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      First, Last     : Source_Ptr);
   --  same as above, but take the node range in argument

   procedure Insert_With_Next
     (Kind            : Annotate_Kind;
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
            return;

         --  there is nothing to do in this case, but there may be other ranges
         --  later which may still be interesting.

         else
            null;
         end if;
      end loop;
   end Check_Is_Annotated;

   ---------------------------
   -- Insert_Annotate_Range --
   ---------------------------

   procedure Insert_Annotate_Range
     (Kind            : Annotate_Kind;
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
         Insert_Annotate_Range (Kind, Pattern, Reason,
                                Specification (Range_Node));
         Insert_Annotate_Range (Kind, Pattern, Reason,
                                Handled_Statement_Sequence (Range_Node));
         Insert_Annotate_Range (Kind, Pattern, Reason,
                                Declarations (Range_Node));
         Insert_With_Next (Kind, Pattern, Reason,
                           Parent (Parent (Corresponding_Spec (Range_Node))));
         return;
      end if;
      Sloc_Range (Range_Node, First_Sloc, Last_Sloc);
      Insert_Annotate_Range (Kind, Pattern, Reason, First_Sloc, Last_Sloc);
   end Insert_Annotate_Range;

   procedure Insert_Annotate_Range
     (Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      First, Last     : Source_Ptr)
   is

      use Annot_Range_Vectors;

      Cur : Cursor := Annotations.First;
   begin
      while Has_Element (Cur) and then First > Element (Cur).First loop
         Next (Cur);
      end loop;
      Annotations.Insert
        (Cur,
         (Kind    => Kind,
          First   => First,
          Last    => Last,
          Pattern => Pattern,
          Reason  => Reason));
   end Insert_Annotate_Range;

   procedure Insert_Annotate_Range
     (Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      List            : List_Id)
   is
      First_Sloc, Last_Sloc, Tmp : Source_Ptr;
   begin
      if Present (List) then
         Sloc_Range (First (List), First_Sloc, Tmp);
         Sloc_Range (Last (List), Tmp, Last_Sloc);
      end if;
      Insert_Annotate_Range (Kind, Pattern, Reason, First_Sloc, Last_Sloc);
   end Insert_Annotate_Range;

   ----------------------
   -- Insert_With_Next --
   ----------------------

   procedure Insert_With_Next
     (Kind            : Annotate_Kind;
      Pattern, Reason : String_Id;
      First_Node      : Node_Id)
   is
      Node : Node_Id := First_Node;
   begin
      Insert_Annotate_Range (Kind, Pattern, Reason, Node);
      Next (Node);
      while Present (Node) and not Comes_From_Source (Node) loop
         Insert_Annotate_Range (Kind, Pattern, Reason, Node);
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
         Insert_With_Next (Kind, Pattern, Reason, Preceding);
      else
         Insert_Annotate_Range (Kind, Pattern, Reason, Preceding);
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
