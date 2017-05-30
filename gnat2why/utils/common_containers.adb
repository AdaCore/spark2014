------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    C O M M O N _ C O N T A I N E R S                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2014-2017, Altran UK Limited                 --
--               Copyright (C) 2014-2017, AdaCore                           --
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
------------------------------------------------------------------------------

with GNATCOLL.Symbols; use GNATCOLL.Symbols;
with Sem_Util;         use Sem_Util;
with SPARK_Xrefs;      use SPARK_Xrefs;

package body Common_Containers is

   package Symbol_To_Entity_Name_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Symbol,
      Element_Type    => Entity_Name,
      Hash            => GNATCOLL.Symbols.Hash,
      Equivalent_Keys => "=");

   package Entity_Id_To_Entity_Name_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Entity_Name,
      Hash            => Node_Hash,
      Equivalent_Keys => "=");

   package Entity_Name_To_Symbol_Vectors is new Ada.Containers.Vectors
     (Index_Type   => Entity_Name,
      Element_Type => Symbol);

   Intern_Strings : constant Symbol_Table_Access := Allocate;

   Symbol_Cache : Symbol_To_Entity_Name_Maps.Map;
   String_Cache : Entity_Name_To_Symbol_Vectors.Vector;
   Name_Cache   : Entity_Id_To_Entity_Name_Maps.Map;

   --------------------
   -- To_Entity_Name --
   --------------------

   function To_Entity_Name (S : String) return Entity_Name is
      Sym : constant Symbol := Intern_Strings.Find (S);

      Position : Symbol_To_Entity_Name_Maps.Cursor;
      Inserted : Boolean;

      Next_Num : constant Entity_Name := String_Cache.Last_Index + 1;

   begin
      Symbol_Cache.Insert (Key       => Sym,
                           New_Item  => Next_Num,
                           Position  => Position,
                           Inserted  => Inserted);

      if Inserted then
         String_Cache.Append (Sym);

         return Next_Num;
      else
         return Symbol_Cache (Position);
      end if;
   end To_Entity_Name;

   function To_Entity_Name (E : Entity_Id) return Entity_Name is
      Position : Entity_Id_To_Entity_Name_Maps.Cursor;
      Inserted : Boolean;
   begin
      Name_Cache.Insert (Key      => E,
                         New_Item => Entity_Name'Last, -- dummy value
                         Position => Position,
                         Inserted => Inserted);

      if Inserted then
         Name_Cache (Position) := To_Entity_Name (Unique_Name (E));
      end if;

      return Name_Cache (Position);
   end To_Entity_Name;

   ---------------
   -- To_String --
   ---------------

   function To_String (E : Entity_Name) return String is
   begin
      return Get (String_Cache (E)).all;
   end To_String;

   -----------------
   -- To_Name_Set --
   -----------------

   function To_Name_Set (S : Node_Sets.Set) return Name_Sets.Set is
   begin
      return X : Name_Sets.Set := Name_Sets.Empty_Set do
         for E of S loop
            X.Insert (if Present (E)
                      then To_Entity_Name (E)
                      else To_Entity_Name (Name_Of_Heap_Variable));
         end loop;
      end return;
   end To_Name_Set;

end Common_Containers;
