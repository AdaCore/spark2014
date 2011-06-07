------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                          E X P L A N A T I O N S                         --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or modify it  --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnatprove is distributed in the hope that it will  be  useful,  --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

with Ada.IO_Exceptions;
with Ada.Strings;
with Ada.Strings.Fixed; use Ada.Strings.Fixed;
with Ada.Strings.Maps;
with Ada.Text_IO;

with String_Utils;      use String_Utils;

package body Explanations is

   function Interpret_Why_VC_Kind (S : String) return VC_Kind;
   --  Parse a Why explanation string and transform it into a VC_Kind.

   procedure Print_VC_Msg (V : VC_Kind);
   --  Print an explanation for the VC kind

   ------------------------
   -- Get_VC_Explanation --
   ------------------------

   function Get_VC_Explanation (Expl_File : String) return Explanation
   is
      use Ada.Text_IO;
      File : File_Type;
      Expl : Explanation;

      Char_Set : constant Ada.Strings.Maps.Character_Set :=
         Ada.Strings.Maps.To_Set (""" ");
   begin
      Open (File, In_File, Expl_File);
      while True loop
         declare
            S : constant String := Get_Line (File);
         begin
            if Starts_With (S, "file") then
               Expl.EX_Filename :=
                  new String'(Trim (S (7 .. S'Last), Char_Set, Char_Set));
            elsif Starts_With (S, "line") then
               Expl.EX_Line :=
                  new String'(Trim (S (7 .. S'Last), Char_Set, Char_Set));
            elsif Starts_With (S, "begin") then
               Expl.EX_Col :=
                  new String'(Trim (S (8 .. S'Last), Char_Set, Char_Set));
            elsif Starts_With (S, "kind") then
               Expl.EX_Kind :=
                  Interpret_Why_VC_Kind
                    (Trim (S (7 .. S'Last), Char_Set, Char_Set));
            elsif Starts_With (S, "text") then
               Expl.EX_Kind :=
                 VC_Kind'Value (Trim (S (7 .. S'Last), Char_Set, Char_Set));
            end if;
         end;
      end loop;
      Close (File);
      return Expl;
   exception
      when Ada.IO_Exceptions.End_Error =>
         return Expl;
   end Get_VC_Explanation;

   ---------------------------
   -- Interpret_Why_VC_Kind --
   ---------------------------

   function Interpret_Why_VC_Kind (S : String) return VC_Kind
   is
   begin
      if S = "Lemma" or else S = "Assert" or else S = "Check" then
         return VC_Assert;
      elsif S = "Pre" then
         return VC_Precondition;
      elsif S = "Post" then
         return VC_Postcondition;
      elsif S = "LoopInvInit" then
         return VC_Loop_Invariant_Init;
      elsif S = "LoopInvPreserv" then
         return VC_Loop_Invariant_Preserv;
      else
         raise Program_Error;
      end if;
   end Interpret_Why_VC_Kind;

   ---------------------
   -- Print_Error_Msg --
   ---------------------

   procedure Print_Error_Msg (X : Explanation; Proved : Boolean := False) is
      use Ada.Text_IO;
   begin
      Put (X.EX_Filename.all);
      Put (":");
      Put (X.EX_Line.all);
      Put (":");
      Put (X.EX_Col.all);
      Put (":");
      if Proved then
         Put (" (info) ");
      else
         Put (" ");
      end if;
      Print_VC_Msg (X.EX_Kind);
      if Proved then
         Put_Line (" proved");
      else
         Put_Line (" not proved");
      end if;
   end Print_Error_Msg;

   ------------------
   -- Print_VC_Msg --
   ------------------

   procedure Print_VC_Msg (V : VC_Kind)
   is
      use Ada.Text_IO;
   begin
      case V is
         when VC_Unused =>
            raise Program_Error;

         when VC_Overflow_Check =>
            Put ("overflow check");

         when VC_Range_Check =>
            Put ("range check");

         when VC_Array_Bounds_Check =>
            Put ("array bounds check");

         when VC_Division_By_Zero =>
            Put ("division by zero");

         when VC_Precondition =>
            Put ("precondition");

         when VC_Postcondition =>
            Put ("postcondition");

         when VC_Loop_Invariant =>
            Put ("loop invariant");

         when VC_Loop_Invariant_Init =>
            Put ("loop invariant initalization");

         when VC_Loop_Invariant_Preserv =>
            Put ("loop invariant preservation");

         when VC_Assert =>
            Put ("assertion");
      end case;
   end Print_VC_Msg;

end Explanations;
