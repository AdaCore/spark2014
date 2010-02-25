------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--                       S P A R K I F Y . B A S I C                        --
--                                                                          --
--                                 S p e c                                  --
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

--  This package contains declarations of entities which are used in more than
--  one Sparkify component

with Ada.Wide_Text_IO;  use Ada.Wide_Text_IO;

with Table;

with Asis;        use Asis;
with Asis.Text;   use Asis.Text;

package Sparkify.Basic is

   Not_Implemented_Yet : exception;
   --  For development period only

   The_Unit        : Asis.Compilation_Unit;
   --  The current compilation unit

   The_Last_Line   : Line_Number_Positive;
   --  The number of the last line of The_Unit

   The_Last_Column : Character_Position;
   --  The number of the last column of the last line of The_Unit

   Result_Out_File : File_Type;
   --  The result file in case the result should be written into a disk
   --  file

   Result_Name_In_Output : Wide_String := "Result";

   type Keyword_Kinds is
   --  Ada keywords
     (Not_A_KW,
      KW_Abort,
      KW_Abs,
      KW_Abstract,
      KW_Accept,
      KW_Access,
      KW_Aliased,
      KW_All,
      KW_And,
      KW_Array,
      KW_At,
      KW_Begin,
      KW_Body,
      KW_Case,
      KW_Constant,
      KW_Declare,
      KW_Delay,
      KW_Delta,
      KW_Digits,
      KW_Do,
      KW_Else,
      KW_Elsif,
      KW_End,
      KW_Entry,
      KW_Exception,
      KW_Exit,
      KW_For,
      KW_Function,
      KW_Generic,
      KW_Goto,
      KW_If,
      KW_In,
      KW_Is,
      KW_Limited,
      KW_Loop,
      KW_Mod,
      KW_New,
      KW_Not,
      KW_Null,
      KW_Of,
      KW_Or,
      KW_Others,
      KW_Out,
      KW_Package,
      KW_Pragma,
      KW_Private,
      KW_Procedure,
      KW_Protected,
      KW_Raise,
      KW_Range,
      KW_Record,
      KW_Rem,
      KW_Renames,
      KW_Requeue,
      KW_Return,
      KW_Reverse,
      KW_Select,
      KW_Separate,
      KW_Subtype,
      KW_Tagged,
      KW_Task,
      KW_Terminate,
      KW_Then,
      KW_Type,
      KW_Until,
      KW_Use,
      KW_When,
      KW_While,
      KW_With,
      KW_Xor,

      --  Ada 2005 keywords:
      KW_Interface,
      KW_Overriding,
      KW_Synchronized);

   Abort_String     : Program_Text := "abort";
   Abs_String       : Program_Text := "abs";
   Abstract_String  : Program_Text := "abstract";
   Accept_String    : Program_Text := "accept";
   Access_String    : Program_Text := "access";
   Aliased_String   : Program_Text := "aliased";
   All_String       : Program_Text := "all";
   And_String       : Program_Text := "and";
   Array_String     : Program_Text := "array";
   At_String        : Program_Text := "at";
   Begin_String     : Program_Text := "begin";
   Body_String      : Program_Text := "body";
   Case_String      : Program_Text := "case";
   Constant_String  : Program_Text := "constant";
   Declare_String   : Program_Text := "declare";
   Delay_String     : Program_Text := "delay";
   Delta_String     : Program_Text := "delta";
   Digits_String    : Program_Text := "digits";
   Do_String        : Program_Text := "do";
   Else_String      : Program_Text := "else";
   Elsif_String     : Program_Text := "elsif";
   End_String       : Program_Text := "end";
   Entry_String     : Program_Text := "entry";
   Exception_String : Program_Text := "exception";
   Exit_String      : Program_Text := "exit";
   For_String       : Program_Text := "for";
   Function_String  : Program_Text := "function";
   Generic_String   : Program_Text := "generic";
   Goto_String      : Program_Text := "goto";
   If_String        : Program_Text := "if";
   In_String        : Program_Text := "in";
   KW_Is_String     : Program_Text := "is";
   Limited_String   : Program_Text := "limited";
   Loop_String      : Program_Text := "loop";
   Mod_String       : Program_Text := "mod";
   New_String       : Program_Text := "new";
   Not_String       : Program_Text := "not";
   Null_String      : Program_Text := "null";
   Of_String        : Program_Text := "of";
   Or_String        : Program_Text := "or";
   Others_String    : Program_Text := "others";
   Out_String       : Program_Text := "out";
   Package_String   : Program_Text := "package";
   Pragma_String    : Program_Text := "pragma";
   Private_String   : Program_Text := "private";
   Procedure_String : Program_Text := "procedure";
   Protected_String : Program_Text := "protected";
   Raise_String     : Program_Text := "raise";
   Range_String     : Program_Text := "range";
   Record_String    : Program_Text := "record";
   Rem_String       : Program_Text := "rem";
   Renames_String   : Program_Text := "renames";
   Requeue_String   : Program_Text := "requeue";
   Return_String    : Program_Text := "return";
   Reverse_String   : Program_Text := "reverse";
   Select_String    : Program_Text := "select";
   Separate_String  : Program_Text := "separate";
   Subtype_String   : Program_Text := "subtype";
   Tagged_String    : Program_Text := "tagged";
   Task_String      : Program_Text := "task";
   Terminate_String : Program_Text := "terminate";
   Then_String      : Program_Text := "then";
   Type_String      : Program_Text := "type";
   Until_String     : Program_Text := "until";
   Use_String       : Program_Text := "use";
   When_String      : Program_Text := "when";
   While_String     : Program_Text := "while";
   With_String      : Program_Text := "with";
   Xor_String       : Program_Text := "xor";

   --  Ada 2005 keywords:
   Interface_String    : Program_Text := "interface";
   Overriding_String   : Program_Text := "overriding";
   Synchronized_String : Program_Text := "synchronized";

   type Delimiter_Kinds is
   --  Ada delimiters
     (Not_A_Dlm,
      Sharp_Dlm,                --  #
      Ampersand_Dlm,            --  &
      Tick_Dlm,                 --  '
      Left_Parenthesis_Dlm,     --  (
      Right_Parenthesis_Dlm,    --  )
      Asterisk_Dlm,             --  *
      Plus_Dlm,                 --  +
      Comma_Dlm,                --  ,
      Minus_Dlm,                --  -
      Dot_Dlm,                  --  .
      Divide_Dlm,               --  /
      Colon_Dlm,                --  :
      Semicolon_Dlm,            --  ;
      Less_Than_Dlm,            --  <
      Equals_Dlm,               --  =
      Greater_Than_Dlm,         --  >
      Vertical_Line_Dlm,        --  |
      Exclamation_Mark_Dlm,     --  ! as a replacement for |, see RM 95 J.2
      Arrow_Dlm,                --  =>
      Double_Dot_Dlm,           --  ..
      Double_Star_Dlm,          --  **
      Assignment_Dlm,           --  :=
      Inequality_Dlm,           --  /=
      Greater_Or_Equal_Dlm,     --  >=
      Less_Or_Equal_Dlm,        --  <=
      Left_Label_Bracket_Dlm,   --  <<
      Right_Label_Bracket_Dlm,  --  >>
      Box_Dlm);                 --  <>

   function Is_White_Space (W_Ch : Wide_Character) return Boolean;
   --  Checks if the argument is a blank character (space, HT, FF or VT)

   package Lines_Table is new Table.Table
     (Table_Component_Type => Asis.Text.Line,
      Table_Index_Type     => Line_Number_Positive,
      Table_Low_Bound      => 1,
      Table_Initial        => 100,
      Table_Increment      => 100,
      Table_Name           => "");

end Sparkify.Basic;
