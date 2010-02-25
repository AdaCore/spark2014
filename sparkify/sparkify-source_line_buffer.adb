------------------------------------------------------------------------------
--                                                                          --
--                            SPARKIFY COMPONENTS                           --
--                                                                          --
--         S P A R K I F Y . S O U R C E _ L I N E _ B U F F E R            --
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

package body Sparkify.Source_Line_Buffer is

   -------------------
   -- Is_White_Text --
   -------------------

   function Is_White_Text (Text : Asis.Program_Text) return Boolean is
   begin
      for J in Text'Range loop
         if not Is_White_Space (Text (J)) then
            return False;
         end if;
      end loop;
      return True;
   end Is_White_Text;

   --------------------
   -- Skip_Delimiter --
   --------------------

   procedure Skip_Delimiter (C : in out Cursor; DL : Delimiter_Kinds) is
   begin
      Skip_Blanks (C);

      case DL is
         when Not_A_Dlm               => null;
         when Sharp_Dlm               => Skip_Word (C, "#");
         when Ampersand_Dlm           => Skip_Word (C, "&");
         when Tick_Dlm                => Skip_Word (C, "'");
         when Left_Parenthesis_Dlm    => Skip_Word (C, "(");
         when Right_Parenthesis_Dlm   => Skip_Word (C, ")");
         when Asterisk_Dlm            => Skip_Word (C, "*");
         when Plus_Dlm                => Skip_Word (C, "+");
         when Comma_Dlm               => Skip_Word (C, ",");
         when Minus_Dlm               => Skip_Word (C, "-");
         when Dot_Dlm                 => Skip_Word (C, ".");
         when Divide_Dlm              => Skip_Word (C, "/");
         when Colon_Dlm               => Skip_Word (C, ":");
         when Semicolon_Dlm           => Skip_Word (C, ";");
         when Less_Than_Dlm           => Skip_Word (C, "<");
         when Equals_Dlm              => Skip_Word (C, "=");
         when Greater_Than_Dlm        => Skip_Word (C, ">");
         when Vertical_Line_Dlm       => Skip_Word (C, "|");
         when Exclamation_Mark_Dlm    => Skip_Word (C, "!");
         when Arrow_Dlm               => Skip_Word (C, "=>");
         when Double_Dot_Dlm          => Skip_Word (C, "..");
         when Double_Star_Dlm         => Skip_Word (C, "**");
         when Assignment_Dlm          => Skip_Word (C, ":=");
         when Inequality_Dlm          => Skip_Word (C, "/=");
         when Greater_Or_Equal_Dlm    => Skip_Word (C, ">=");
         when Less_Or_Equal_Dlm       => Skip_Word (C, "<=");
         when Left_Label_Bracket_Dlm  => Skip_Word (C, "<<");
         when Right_Label_Bracket_Dlm => Skip_Word (C, ">>");
         when Box_Dlm                 => Skip_Word (C, "<>");
      end case;

   end Skip_Delimiter;

   ------------------
   -- Skip_Keyword --
   ------------------

   procedure Skip_Keyword (C : in out Cursor; KW : Keyword_Kinds) is
   begin
      Skip_Blanks (C);

      case KW is
         when Not_A_KW     => null;
         when KW_Abort     => Skip_Word (C, Abort_String);
         when KW_Abs       => Skip_Word (C, Abs_String);
         when KW_Abstract  => Skip_Word (C, Abstract_String);
         when KW_Accept    => Skip_Word (C, Accept_String);
         when KW_Access    => Skip_Word (C, Access_String);
         when KW_Aliased   => Skip_Word (C, Aliased_String);
         when KW_All       => Skip_Word (C, All_String);
         when KW_And       => Skip_Word (C, And_String);
         when KW_Array     => Skip_Word (C, Array_String);
         when KW_At        => Skip_Word (C, At_String);
         when KW_Begin     => Skip_Word (C, Begin_String);
         when KW_Body      => Skip_Word (C, Body_String);
         when KW_Case      => Skip_Word (C, Case_String);
         when KW_Constant  => Skip_Word (C, Constant_String);
         when KW_Declare   => Skip_Word (C, Declare_String);
         when KW_Delay     => Skip_Word (C, Delay_String);
         when KW_Delta     => Skip_Word (C, Delta_String);
         when KW_Digits    => Skip_Word (C, Digits_String);
         when KW_Do        => Skip_Word (C, Do_String);
         when KW_Else      => Skip_Word (C, Else_String);
         when KW_Elsif     => Skip_Word (C, Elsif_String);
         when KW_End       => Skip_Word (C, End_String);
         when KW_Entry     => Skip_Word (C, Entry_String);
         when KW_Exception => Skip_Word (C, Exception_String);
         when KW_Exit      => Skip_Word (C, Exit_String);
         when KW_For       => Skip_Word (C, For_String);
         when KW_Function  => Skip_Word (C, Function_String);
         when KW_Generic   => Skip_Word (C, Generic_String);
         when KW_Goto      => Skip_Word (C, Goto_String);
         when KW_If        => Skip_Word (C, If_String);
         when KW_In        => Skip_Word (C, In_String);
         when KW_Is        => Skip_Word (C, KW_Is_String);
         when KW_Limited   => Skip_Word (C, Limited_String);
         when KW_Loop      => Skip_Word (C, Loop_String);
         when KW_Mod       => Skip_Word (C, Mod_String);
         when KW_New       => Skip_Word (C, New_String);
         when KW_Not       => Skip_Word (C, Not_String);
         when KW_Null      => Skip_Word (C, Null_String);
         when KW_Of        => Skip_Word (C, Of_String);
         when KW_Or        => Skip_Word (C, Or_String);
         when KW_Others    => Skip_Word (C, Others_String);
         when KW_Out       => Skip_Word (C, Out_String);
         when KW_Package   => Skip_Word (C, Package_String);
         when KW_Pragma    => Skip_Word (C, Pragma_String);
         when KW_Private   => Skip_Word (C, Private_String);
         when KW_Procedure => Skip_Word (C, Procedure_String);
         when KW_Protected => Skip_Word (C, Protected_String);
         when KW_Raise     => Skip_Word (C, Raise_String);
         when KW_Range     => Skip_Word (C, Range_String);
         when KW_Record    => Skip_Word (C, Record_String);
         when KW_Rem       => Skip_Word (C, Rem_String);
         when KW_Renames   => Skip_Word (C, Renames_String);
         when KW_Requeue   => Skip_Word (C, Requeue_String);
         when KW_Return    => Skip_Word (C, Return_String);
         when KW_Reverse   => Skip_Word (C, Reverse_String);
         when KW_Select    => Skip_Word (C, Select_String);
         when KW_Separate  => Skip_Word (C, Separate_String);
         when KW_Subtype   => Skip_Word (C, Subtype_String);
         when KW_Tagged    => Skip_Word (C, Tagged_String);
         when KW_Task      => Skip_Word (C, Task_String);
         when KW_Terminate => Skip_Word (C, Terminate_String);
         when KW_Then      => Skip_Word (C, Then_String);
         when KW_Type      => Skip_Word (C, Type_String);
         when KW_Until     => Skip_Word (C, Until_String);
         when KW_Use       => Skip_Word (C, Use_String);
         when KW_When      => Skip_Word (C, When_String);
         when KW_While     => Skip_Word (C, While_String);
         when KW_With      => Skip_Word (C, With_String);
         when KW_Xor       => Skip_Word (C, Xor_String);

         --  Ada 2005 keywords:
         when KW_Interface    => Skip_Word (C, Interface_String);
         when KW_Overriding   => Skip_Word (C, Overriding_String);
         when KW_Synchronized => Skip_Word (C, Synchronized_String);
      end case;

   end Skip_Keyword;

end Sparkify.Source_Line_Buffer;
