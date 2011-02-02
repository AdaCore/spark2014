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

with Atree;                use Atree;
with Namet;                use Namet;
with Sinput;               use Sinput;
with Why.Atree.Accessors;  use Why.Atree.Accessors;
with Why.Atree.Builders;   use Why.Atree.Builders;
with Why.Atree.Tables;     use Why.Atree.Tables;

package body Gnat2Why.Locs is

   Prefix : constant String := "Gnat2why__";
   --  The prefix used for located labels

   Counter : Positive := 1;
   --  The counter used to generate fresh names

   Located_Labels : constant W_Identifier_List := New_List;

   function Int_Image (N : Integer) return String;
   --  Generate a string from an Integer, without the leading space.

   procedure Print_Located_Label
      (O : Output_Id;
       I : W_Identifier_Id);
   --  Print a single entry of a located label

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

   function New_Located_Label (N : Node_Id) return W_Identifier_Id
   is
      Result : W_Identifier_Id;
   begin
      Name_Len := 0;
      Add_Str_To_Name_Buffer (Prefix & Int_Image (Counter));
      Result := New_Identifier (Ada_Node => N, Symbol => Name_Find);
      Append (Located_Labels, Result);
      Counter := Counter + 1;
      return Duplicate_Identifier (Ada_Node => N, Id => Result);
   end New_Located_Label;

   procedure Print_Located_Label
      (O : Output_Id;
       I : W_Identifier_Id)
   is
      N   : constant Node_Id := Get_Ada_Node (I);
      Loc : constant Source_Ptr := Sloc (N);
   begin
      P (O, "[");
      P (O, Get_Name_String (Get_Node (I).Symbol));
      P (O, "]");
      --  file, line, begin, end, name (optional)
      NL (O);
      P (O, "file = """);
      P (O, Get_Name_String (Full_File_Name (Get_Source_File_Index (Loc))));
      P (O, """");
      NL (O);
      P (O, "line = ");
      P (O, Physical_Line_Number'Image (Get_Physical_Line_Number (Loc)));
      P (O, "");
      NL (O);
      P (O, "begin = ");
      P (O, Column_Number'Image (Get_Column_Number (Loc)));
      P (O, "");
      NL (O);
   end Print_Located_Label;

   ---------------------------
   -- Print_Locations_Table --
   ---------------------------

   procedure Print_Locations_Table (O : Output_Id)
   is
      use Node_Lists;
      Labels   : constant List := Get_List (Located_Labels);
      Position : Cursor := First (Labels);
   begin
      while Position /= No_Element loop
         Print_Located_Label (O, Element (Position));
         Next (Position);
      end loop;
   end Print_Locations_Table;

   procedure Print_Label_List (O : Output_Id := Stdout)
   is
      use Node_Lists;
      Labels   : constant List := Get_List (Located_Labels);
      Position : Cursor := First (Labels);
   begin
      while Position /= No_Element loop
         declare
            Cur_Elt : constant W_Identifier_Id := Element (Position);
         begin
            P (O, Get_Name_String (Get_Node (Cur_Elt).Symbol));
            NL (O);
            Next (Position);
         end;
      end loop;
   end Print_Label_List;
end Gnat2Why.Locs;
