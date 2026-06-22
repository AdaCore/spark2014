------------------------------------------------------------------------------
--                                                                          --
--                            GNATPROVE COMPONENTS                          --
--                                                                          --
--                     S P A R K _ J S O N _ E N T I T I E S                --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                     Copyright (C) 2026, AdaCore                          --
--                                                                          --
-- gnatprove is  free  software;  you can redistribute it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnatprove is distributed  in the hope that it will be useful,  --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for more details.  You should have received a copy of the GNU     --
-- General Public License distributed with gnatprove; see file COPYING3. If --
-- not, go to http://www.gnu.org/licenses for a complete copy of the license.--
--                                                                          --
-- gnatprove is maintained by AdaCore (http://www.adacore.com)              --
--                                                                          --
------------------------------------------------------------------------------

package body SPARK_JSON_Entities is

   ------------------------
   -- Parse_Entity_Table --
   ------------------------

   function Parse_Entity_Table
     (Table : JSON_Value) return Entity_Vectors.Vector
   is
      Result : Entity_Vectors.Vector;

      procedure Parse_Entry (Key : UTF8_String; Value : JSON_Value);

      -----------------
      -- Parse_Entry --
      -----------------

      procedure Parse_Entry (Key : UTF8_String; Value : JSON_Value) is
         Item    : Entity_Info;
         JS_Sloc : constant JSON_Array := Get (Get (Value, "sloc"));
      begin
         Item.Key := To_Unbounded_String (String (Key));
         Item.Key_Index := Positive'Value (String (Key));
         Item.Name := To_Unbounded_String (String'(Get (Value, "name")));

         if Has_Field (Value, "manifest_kind") then
            Item.Manifest_Kind :=
              To_Unbounded_String (String'(Get (Value, "manifest_kind")));
         end if;

         if Has_Field (Value, "manifest_profile") then
            Item.Manifest_Profile :=
              To_Unbounded_String (String'(Get (Value, "manifest_profile")));
         end if;

         for Index in 1 .. Length (JS_Sloc) loop
            declare
               JS_Base : constant JSON_Value := Get (JS_Sloc, Index);
            begin
               Item.Sloc.Append
                 (Entity_Sloc'
                    (File   =>
                       To_Unbounded_String (String'(Get (JS_Base, "file"))),
                     Line   => Positive'(Get (JS_Base, "line")),
                     Column => Positive'(Get (JS_Base, "column"))));
            end;
         end loop;

         Result.Append (Item);
      end Parse_Entry;

   begin
      Map_JSON_Object (Table, Parse_Entry'Access);
      return Result;
   end Parse_Entity_Table;

end SPARK_JSON_Entities;
