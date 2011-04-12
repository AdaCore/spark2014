------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                      G N A T 2 W H Y - L O C S                           --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                       Copyright (C) 2010-2011, AdaCore                   --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute it and/or modify it   --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software Foundation;  either version  2,  or  (at your option) any later --
-- version. gnat2why is distributed in the hope that it will  be  useful,   --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHAN-  --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License  for more details. You  should  have  received a copy of the GNU --
-- General Public License  distributed with GNAT; see file COPYING. If not, --
-- write to the Free Software Foundation,  51 Franklin Street, Fifth Floor, --
-- Boston,                                                                  --
--                                                                          --
-- gnat2why is maintained by AdaCore (http://www.adacore.com)               --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers.Doubly_Linked_Lists;
with Atree;                use Atree;
with Namet;                use Namet;
with Sinput;               use Sinput;
with Why.Atree.Accessors;  use Why.Atree.Accessors;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Atree.Tables;     use Why.Atree.Tables;
with Why.Conversions;      use Why.Conversions;

package body Gnat2Why.Locs is

   Prefix : constant String := "Gnat2why__";
   --  The prefix used for located labels

   Counter : Positive := 1;
   --  The counter used to generate fresh names

   type Label is
      record
         Label_Ident  : W_Identifier_Id;
         Label_Reason : VC_Kind;
      end record;

   package Label_Lists is
      new Ada.Containers.Doubly_Linked_Lists (Element_Type => Label);

   Located_Labels : Label_Lists.List := Label_Lists.Empty_List;

   function Explanation_Of_VC_Kind (V : VC_Kind) return String;
   --  Transform a VC_Kind into a string.

   function Int_Image (N : Integer) return String;
   --  Generate a string from an Integer, without the leading space.

   procedure Print_Located_Label
      (O : Output_Id;
       L : Label);
   --  Print a single entry of a located label

   ----------------------------
   -- Explanation_Of_VC_Kind --
   ----------------------------

   function Explanation_Of_VC_Kind (V : VC_Kind) return String
   is
   begin
      case V is
         when VC_Overflow_Check =>
            return "Overflow Check";

         when VC_Range_Check =>
            return "Range Check";

         when VC_Array_Bounds_Check =>
            return "Array Bounds Check";

         when VC_Division_By_Zero =>
            return "Division by Zero";

         when VC_Precondition =>
            return "Precondition";

         when VC_Postcondition =>
            return "Postcondition";

         when VC_Loop_Invariant =>
            return "Loop Invariant";

         when VC_Assert =>
            return "Loop Invariant";
      end case;
   end Explanation_Of_VC_Kind;

   ---------------
   -- Int_Image --
   ---------------

   function Int_Image (N : Integer) return String is
      Result : constant String := Integer'Image (N);
   begin
      if N >= 0 then
         return Result (2 .. Result'Last);
      else
         return Result;
      end if;
   end Int_Image;

   -----------------------
   -- New_Located_Label --
   -----------------------

   function New_Located_Label (N : Node_Id; Reason : VC_Kind)
      return W_Identifier_Id
   is
      use Label_Lists;
      L : Label;
   begin
      Name_Len := 0;
      Add_Str_To_Name_Buffer (Prefix & Int_Image (Counter));
      L.Label_Ident := New_Identifier (Ada_Node => N, Symbol => Name_Find);
      L.Label_Reason := Reason;
      Append (Located_Labels, L);
      Counter := Counter + 1;
      return L.Label_Ident;
   end New_Located_Label;

   procedure Print_Located_Label
      (O : Output_Id;
       L : Label)
   is
      procedure Write_Field (Key, Value : String; Protect : Boolean := False);
      --  Write a key/value pair to the file in argument.

      procedure Write_Field (Key, Value : String; Protect : Boolean := False)
      is
      begin
         P (O, Key);
         P (O, " = ");
         if Protect then
            P (O, """");
         end if;
         P (O, Value);
         if Protect then
            P (O, """");
         end if;
         NL (O);
      end Write_Field;

      I    : constant W_Identifier_Id := L.Label_Ident;
      N    : constant Node_Id := Get_Ada_Node (+I);
      Loc  : constant Source_Ptr := Sloc (N);
      Name : constant String := Get_Name_String (Get_Node (+I).Symbol);

      --  beginning of processing for Print_Located_Label;
   begin
      P (O, "[");
      P (O, Name);
      P (O, "]");
      NL (O);
      Write_Field
        ("file",
         Get_Name_String (File_Name (Get_Source_File_Index (Loc))),
         True);
      Write_Field
        ("line",
         Physical_Line_Number'Image (Get_Physical_Line_Number (Loc)));
      Write_Field ("begin", Column_Number'Image (Get_Column_Number (Loc)));
      Write_Field
        ("kind",
         Explanation_Of_VC_Kind (L.Label_Reason),
         True);
   end Print_Located_Label;

   ---------------------------
   -- Print_Locations_Table --
   ---------------------------

   procedure Print_Locations_Table (O : Output_Id)
   is
      use Label_Lists;
      Position : Cursor := First (Located_Labels);
   begin
      while Position /= No_Element loop
         Print_Located_Label (O, Element (Position));
         Next (Position);
      end loop;
   end Print_Locations_Table;

   procedure Print_Label_List (O : Output_Id := Stdout)
   is
      use Label_Lists;
      Position : Cursor := First (Located_Labels);
   begin
      while Position /= No_Element loop
         declare
            Cur_Elt : constant W_Identifier_Id :=
               Element (Position).Label_Ident;
         begin
            P (O, Get_Name_String (Get_Node (+Cur_Elt).Symbol));
            NL (O);
            Next (Position);
         end;
      end loop;
   end Print_Label_List;
end Gnat2Why.Locs;
