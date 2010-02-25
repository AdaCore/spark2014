------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                    S P A R K I F Y . P P _ O U T P U T                   --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2009-2010, AdaCore                     --
--                                                                          --
-- Sparkify is  free  software;  you can redistribute it  and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. Sparkify is distributed in the hope that it will be useful, but --
-- WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHANTABI- --
-- LITY or  FITNESS  FOR A  PARTICULAR  PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- Sparkify is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Wide_Text_IO;                 use Ada.Wide_Text_IO;
with Ada.Strings.Wide_Fixed;           use Ada.Strings.Wide_Fixed;

with Sparkify.State;                   use Sparkify.State;
with Sparkify.Source_Traversal;        use Sparkify.Source_Traversal;
with Sparkify.Common;                  use Sparkify.Common;

package body Sparkify.PP_Output is

   -------------------
   -- PP_Close_Line --
   -------------------

   procedure PP_Close_Line (Increase_Count : Boolean := True) is
   begin
      New_Line;
      if Increase_Count then
         Output_Line := Output_Line + 1;
      end if;
      Output_Column := 1;
   end PP_Close_Line;

   --------------
   -- PP_Space --
   --------------

   procedure PP_Space is
   begin
      Put (" ");
      Output_Column := Output_Column + 1;
   end PP_Space;

   ------------
   -- PP_Pad --
   ------------

   procedure PP_Pad (N : Natural) is
   begin
      for J in 1 .. N loop
         Put (" ");
      end loop;
      Output_Column := Output_Column + N;
   end PP_Pad;

   -------------
   -- PP_Word --
   -------------

   procedure PP_Word (S : Program_Text) is
   begin
      Put (S);
      Output_Column := Output_Column + S'Length;
   end PP_Word;

   ------------------
   -- PP_Delimiter --
   ------------------

   procedure PP_Delimiter (DL : Delimiter_Kinds) is
   begin

      case DL is
         when Not_A_Dlm               => null;
         when Sharp_Dlm               => PP_Word ("#");
         when Ampersand_Dlm           => PP_Word ("&");
         when Tick_Dlm                => PP_Word ("'");
         when Left_Parenthesis_Dlm    => PP_Word ("(");
         when Right_Parenthesis_Dlm   => PP_Word (")");
         when Asterisk_Dlm            => PP_Word ("*");
         when Plus_Dlm                => PP_Word ("+");
         when Comma_Dlm               => PP_Word (",");
         when Minus_Dlm               => PP_Word ("-");
         when Dot_Dlm                 => PP_Word (".");
         when Divide_Dlm              => PP_Word ("/");
         when Colon_Dlm               => PP_Word (":");
         when Semicolon_Dlm           => PP_Word (";");
         when Less_Than_Dlm           => PP_Word ("<");
         when Equals_Dlm              => PP_Word ("=");
         when Greater_Than_Dlm        => PP_Word (">");
         when Vertical_Line_Dlm       => PP_Word ("|");
         when Exclamation_Mark_Dlm    => PP_Word ("!");
         when Arrow_Dlm               => PP_Word ("=>");
         when Double_Dot_Dlm          => PP_Word ("..");
         when Double_Star_Dlm         => PP_Word ("**");
         when Assignment_Dlm          => PP_Word (":=");
         when Inequality_Dlm          => PP_Word ("/=");
         when Greater_Or_Equal_Dlm    => PP_Word (">=");
         when Less_Or_Equal_Dlm       => PP_Word ("<=");
         when Left_Label_Bracket_Dlm  => PP_Word ("<<");
         when Right_Label_Bracket_Dlm => PP_Word (">>");
         when Box_Dlm                 => PP_Word ("<>");
      end case;

   end PP_Delimiter;

   ----------------
   -- PP_Keyword --
   ----------------

   procedure PP_Keyword (KW : Keyword_Kinds) is
   begin

      case KW is

         when Not_A_KW     => null;
         when KW_Abort     => PP_Word (Abort_String);
         when KW_Abs       => PP_Word (Abs_String);
         when KW_Abstract  => PP_Word (Abstract_String);
         when KW_Accept    => PP_Word (Accept_String);
         when KW_Access    => PP_Word (Access_String);
         when KW_Aliased   => PP_Word (Aliased_String);
         when KW_All       => PP_Word (All_String);
         when KW_And       => PP_Word (And_String);
         when KW_Array     => PP_Word (Array_String);
         when KW_At        => PP_Word (At_String);
         when KW_Begin     => PP_Word (Begin_String);
         when KW_Body      => PP_Word (Body_String);
         when KW_Case      => PP_Word (Case_String);
         when KW_Constant  => PP_Word (Constant_String);
         when KW_Declare   => PP_Word (Declare_String);
         when KW_Delay     => PP_Word (Delay_String);
         when KW_Delta     => PP_Word (Delta_String);
         when KW_Digits    => PP_Word (Digits_String);
         when KW_Do        => PP_Word (Do_String);
         when KW_Else      => PP_Word (Else_String);
         when KW_Elsif     => PP_Word (Elsif_String);
         when KW_End       => PP_Word (End_String);
         when KW_Entry     => PP_Word (Entry_String);
         when KW_Exception => PP_Word (Exception_String);
         when KW_Exit      => PP_Word (Exit_String);
         when KW_For       => PP_Word (For_String);
         when KW_Function  => PP_Word (Function_String);
         when KW_Generic   => PP_Word (Generic_String);
         when KW_Goto      => PP_Word (Goto_String);
         when KW_If        => PP_Word (If_String);
         when KW_In        => PP_Word (In_String);
         when KW_Is        => PP_Word (KW_Is_String);
         when KW_Limited   => PP_Word (Limited_String);
         when KW_Loop      => PP_Word (Loop_String);
         when KW_Mod       => PP_Word (Mod_String);
         when KW_New       => PP_Word (New_String);
         when KW_Not       => PP_Word (Not_String);
         when KW_Null      => PP_Word (Null_String);
         when KW_Of        => PP_Word (Of_String);
         when KW_Or        => PP_Word (Or_String);
         when KW_Others    => PP_Word (Others_String);
         when KW_Out       => PP_Word (Out_String);
         when KW_Package   => PP_Word (Package_String);
         when KW_Pragma    => PP_Word (Pragma_String);
         when KW_Private   => PP_Word (Private_String);
         when KW_Procedure => PP_Word (Procedure_String);
         when KW_Protected => PP_Word (Protected_String);
         when KW_Raise     => PP_Word (Raise_String);
         when KW_Range     => PP_Word (Range_String);
         when KW_Record    => PP_Word (Record_String);
         when KW_Rem       => PP_Word (Rem_String);
         when KW_Renames   => PP_Word (Renames_String);
         when KW_Requeue   => PP_Word (Requeue_String);
         when KW_Return    => PP_Word (Return_String);
         when KW_Reverse   => PP_Word (Reverse_String);
         when KW_Select    => PP_Word (Select_String);
         when KW_Separate  => PP_Word (Separate_String);
         when KW_Subtype   => PP_Word (Subtype_String);
         when KW_Tagged    => PP_Word (Tagged_String);
         when KW_Task      => PP_Word (Task_String);
         when KW_Terminate => PP_Word (Terminate_String);
         when KW_Then      => PP_Word (Then_String);
         when KW_Type      => PP_Word (Type_String);
         when KW_Until     => PP_Word (Until_String);
         when KW_Use       => PP_Word (Use_String);
         when KW_When      => PP_Word (When_String);
         when KW_While     => PP_Word (While_String);
         when KW_With      => PP_Word (With_String);
         when KW_Xor       => PP_Word (Xor_String);

         --  Ada 2005 keywords:
         when KW_Interface    => PP_Word (Interface_String);
         when KW_Overriding   => PP_Word (Overriding_String);
         when KW_Synchronized => PP_Word (Synchronized_String);
      end case;

   end PP_Keyword;

   ----------------
   -- PP_Text_At --
   ----------------

   procedure PP_Text_At
     (Line            : Line_Number_Positive;
      Column          : Character_Position_Positive;
      Text            : Asis.Program_Text;
      Prefix          : Wide_String := "";
      Keep_Only_Blank : Boolean := False)
   is
      Threshold        : constant         := 5;
      Index            : constant Natural := Index_Non_Blank (Text);
      Only_Blank_Chars : constant Boolean := Index = 0;
      Offset           : constant Integer := Index - Text'First;
   begin
      if Text = "" then
         return;
      end if;

      if not Keep_Only_Blank and then Only_Blank_Chars then
         return;
      end if;

      if Line < Output_Line or else
        Line > Output_Line + Threshold then
         PP_Line_Indication (Line);
      elsif Line > Output_Line then
         for J in Integer range Output_Line .. Line - 1 loop
            PP_Close_Line;
         end loop;
      elsif Column < Output_Column then
         PP_Line_Indication (Line);
      end if;

      if Prefix /= "" and then Output_Column = 1 then
         PP_Word (Prefix);
      end if;

      if Column + Offset > Output_Column then
         PP_Pad (Column + Offset - Output_Column);
      end if;

      PP_Word (Text (Index .. Text'Last));
   end PP_Text_At;

   --------------------------
   -- PP_Echo_Cursor_Range --
   --------------------------

   procedure PP_Echo_Cursor_Range
     (From, To : Cursor;
      Prefix   : Wide_String := "")
   is
      Current : Cursor := From;
   begin
      --  Nothing to do if the range is empty
      if Current > To then
         return;
      end if;

      --  Start echoing lines
      loop
         --  Case 1: nothing more to echo
         if Cursor_At_EOF (Current) then
            return;
         end if;

         --  Case 2: last line to echo
         if Cursor_Line (Current) = Cursor_Line (To) then
            PP_Text_At (Cursor_Line (Current), Cursor_Column (Current),
                        Cursor_Line_Range (Current, To),
                        Prefix);
            return;
         end if;

         --  Case 3: more lines to echo
         declare
            End_Of_Line : constant Cursor :=
              Line_Cursor (Kind => After_Line,
                           Line => Cursor_Line (Current));
         begin
            PP_Text_At (Line   => Cursor_Line (Current),
                        Column => Cursor_Column (Current),
                        Text   => Cursor_Line_Range (Current, End_Of_Line),
                        Prefix => Prefix);
            Cursor_Next_Line (Current);
         end;
      end loop;
   end PP_Echo_Cursor_Range;

   ----------------
   -- PP_Inherit --
   ----------------

   procedure PP_Inherit
     (Line   : Line_Number_Positive;
      Column : Character_Position_Positive;
      Text   : Wide_String) is
   begin
      PP_Text_At (Line, Column, "--# inherit ");
      PP_Word (Text & ";");
      PP_Close_Line;
   end PP_Inherit;

   ---------------
   -- PP_Assert --
   ---------------

   procedure PP_Assert
     (Line   : Line_Number_Positive;
      Column : Character_Position_Positive;
      Text   : Wide_String) is
   begin
      PP_Text_At (Line, Column, "--# assert ");
      PP_Word (Text & ";");
      PP_Close_Line;
   end PP_Assert;

   -------------------------
   -- PP_SPARK_Annotation --
   -------------------------

   procedure PP_SPARK_Annotation
     (Column : Character_Position_Positive;
      Expr   : Asis.Expression;
      Intro  : Wide_String);
   --  Send Expr into output stream as a SPARK annotation started with Intro

   procedure PP_SPARK_Annotation
     (Column : Character_Position_Positive;
      Expr   : Asis.Expression;
      Intro  : Wide_String)
   is
      Line : constant Line_Number_Positive := First_Line_Number (Expr);
      Source_Control : Asis.Traverse_Control  := Asis.Continue;
      Padding : constant Wide_String (1 .. Column - 1) := (others => ' ');
      Prefix : constant Wide_String := Padding & "--# ";
      Source_State      : Source_Traversal_State :=
        (Phase       => Printing_Logic,
         Prefix_Len  => Prefix'Length,
         Prefix      => Head (Prefix, Natural (Prefix_Length'Last)),
         Echo_Cursor => Cursor_At (Expr));
   begin
      PP_Text_At (Line, Column, "--# " & Intro & " ");
      Traverse_Source (Expr, Source_Control, Source_State);
      PP_Echo_Cursor_Range (Source_State.Echo_Cursor, Cursor_At_End_Of (Expr),
                            Prefix);
      PP_Word (";");
      PP_Close_Line;
   end PP_SPARK_Annotation;

   --------------
   -- PP_Check --
   --------------

   procedure PP_Check
     (Column : Character_Position_Positive;
      Expr   : Asis.Expression) is
   begin
      PP_SPARK_Annotation (Column, Expr, "check");
   end PP_Check;

   ---------------
   -- PP_Assert --
   ---------------

   procedure PP_Assert
     (Column : Character_Position_Positive;
      Expr   : Asis.Expression) is
   begin
      PP_SPARK_Annotation (Column, Expr, "assert");
   end PP_Assert;

   ---------------------
   -- PP_Precondition --
   ---------------------

   procedure PP_Precondition
     (Column : Character_Position_Positive;
      Expr   : Asis.Expression) is
   begin
      PP_SPARK_Annotation (Column, Expr, "pre");
   end PP_Precondition;

   ----------------------
   -- PP_Postcondition --
   ----------------------

   procedure PP_Postcondition
     (Is_Function : Boolean;
      Column      : Character_Position_Positive;
      Expr        : Asis.Expression) is
   begin
      if Is_Function then
         PP_SPARK_Annotation (Column, Expr,
                              "return " & Result_Name_In_Output & " =>");
      else
         PP_SPARK_Annotation (Column, Expr, "post");
      end if;
   end PP_Postcondition;

   ------------------------
   -- PP_Line_Indication --
   ------------------------

   procedure PP_Line_Indication (Line : Line_Number) is
   begin
      if Output_Column /= 1 then
         PP_Close_Line;
      end if;
      Output_Line := Line;
      PP_Word ("--@ line" & Integer'Wide_Image (Line));
      PP_Close_Line (Increase_Count => False);
   end PP_Line_Indication;

end Sparkify.PP_Output;
