------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                    C O M M O N _ C O N T A I N E R S                     --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--               Copyright (C) 2014-2015, Altran UK Limited                 --
--               Copyright (C) 2014-2015, AdaCore                           --
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

with Ada.Strings.Hash;
with Ada.Unchecked_Deallocation;
with Sem_Util;                   use Sem_Util;

package body Common_Containers is

   function Hash (S : Ada.Strings.Unbounded.String_Access)
                  return Ada.Containers.Hash_Type is
     (Ada.Strings.Hash (S.all));

   function "=" (Left, Right : Ada.Strings.Unbounded.String_Access) return
     Boolean is (Left.all = Right.all);

   procedure Free is new Ada.Unchecked_Deallocation
     (Object => String,
      Name   => Ada.Strings.Unbounded.String_Access);

   package Intern_Strings_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Ada.Strings.Unbounded.String_Access,
      Element_Type    => Entity_Name,
      Hash            => Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   package Entity_Name_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Id,
      Element_Type    => Entity_Name,
      Hash            => Node_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   package Entity_Name_To_String_Maps is new Ada.Containers.Hashed_Maps
     (Key_Type        => Entity_Name,
      Element_Type    => Ada.Strings.Unbounded.String_Access,
      Hash            => Name_Hash,
      Equivalent_Keys => "=",
      "="             => "=");

   Intern_Strings : Intern_Strings_Maps.Map := Intern_Strings_Maps.Empty_Map;
   Num            : Entity_Name := 1;

   Name_Cache     : Entity_Name_Maps.Map := Entity_Name_Maps.Empty_Map;
   String_Cache   : Entity_Name_To_String_Maps.Map :=
     Entity_Name_To_String_Maps.Empty_Map;

   function To_Entity_Name (S : String) return Entity_Name is
      Tmp : Ada.Strings.Unbounded.String_Access := new String'(S);
      use Intern_Strings_Maps;
      C : constant Cursor := Intern_Strings.Find (Tmp);
      use Entity_Name_To_String_Maps;
   begin
      if Has_Element (C) then
         Free (Tmp);
         return Element (C);
      else
         declare
            Rec : constant Entity_Name := Num;
         begin
            String_Cache.Insert (Rec, Tmp);
            Intern_Strings.Insert (Tmp, Rec);
            Num := Num + 1;
            return Rec;
         end;
      end if;
   end To_Entity_Name;

   function To_Entity_Name (E : Entity_Id) return Entity_Name is
      use Entity_Name_Maps;
      C : constant Cursor := Name_Cache.Find (E);
   begin
      if Has_Element (C) then
         return Element (C);
      else
         declare
            Name : constant Entity_Name := To_Entity_Name (Unique_Name (E));
         begin
            Name_Cache.Insert (E, Name);
            return Name;
         end;
      end if;
   end To_Entity_Name;

   function To_String (E : Entity_Name) return String is
      use Entity_Name_To_String_Maps;
   begin
      return Element (String_Cache, E).all;
   end To_String;

end Common_Containers;
