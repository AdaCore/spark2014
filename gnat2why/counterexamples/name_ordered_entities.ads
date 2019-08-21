------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                 N A M E _ O R D E R E D _ E N T I T I E S                --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--                        Copyright (C) 2019, AdaCore                       --
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

with Ada.Containers.Ordered_Sets;
with Ada.Containers.Ordered_Maps;
with Ada.Iterator_Interfaces;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Types;                 use Types;

generic
   type Info is private;
   with function "=" (Left : Info; Right : Info) return Boolean;

package Name_Ordered_Entities is

   --  This package implements a map ordered using the name of elements. The
   --  main differences with a normal map is:
   --  - it can be iterated in the order given by the names of keys
   --  - keys can be added without adding elements (??? to copy the code this
   --      feature replaces : it could disappear in the future)
   --  This datastructure is targeted to counterexamples code. The final
   --  elements are of type Info but in practice this type is always the
   --  general counterexamples type String_CNT_Elements.Map.

   --  ??? S528-030: The implementation is purposefully very similar to the
   --  former code used inside gnat2why-counter_examples. This datastructure
   --  could certainly be improved.

   type Var_Info is private;

   type Variables_Info is tagged private
     with Constant_Indexing => Key,
          Default_Iterator  => Iterate,
          Iterator_Element  => Var_Info;

   type Cursor is private;

   -----------------------------
   -- User provided functions --
   -----------------------------

   function Get_Info (Container : Variables_Info;
                      C         : Cursor)
                      return Info;
   --  Return the Info located at Cursor C. Complexity is O(log (n) ** 2).

   function Has_Info (Container : Variables_Info;
                      C         : Cursor)
                      return Boolean;
   --  The data structure is allowed to have keys without elements (for legacy
   --  reasons). This returns true if an element is present.

   function Id (C : Cursor)
                return Entity_Id;
   --  Returns the Entity_Id associated to the cursor

   function Insert_Info (Container : in out Variables_Info;
                         Id        : Entity_Id;
                         Name      : Unbounded_String;
                         C_Info    : Info)
                         return Cursor;
   --  Add C_Info to the container at key (Id, Name) and return the associated
   --  Cursor. If the (Id, Name) is already associated to an Info then nothing
   --  is done (normal behavior of Container's Insert function).

   function Map_Is_Empty (Container : Variables_Info)
                          return Boolean;
   --  Return true if there is no information at all in the map. Some keys can
   --  be present but no Info is there.

   function Name (C : Cursor)
                  return Unbounded_String;
   --  Returns the name associated to the cursor

   procedure Set_Info (Container : in out Variables_Info;
                       C         : Cursor;
                       C_Info    : Info);
   --  Update the Info located at Cursor C. The complexity is O(log (n) ** 2).
   --  ??? In practice Set_Info is often done after Get_Info: this information
   --  could be used to optimize this call (we could keep the information of
   --  the Entity_Infos.Cursor inside the Cursor type).

   ----------------------------------------------------------
   -- Units necessary for aspects (not intended for users) --
   ----------------------------------------------------------

   function Has_Element (Position : Cursor) return Boolean;
   --  Used only for Iterate

   package Name_Ordered_Iterator_Interfaces is new
     Ada.Iterator_Interfaces (Cursor, Has_Element);

   function Key (Container : Variables_Info;
                 Position  : Cursor)
                 return Var_Info;
   --  Used only for Iterate. Not intended to be used outside of this module

   procedure Iterate
     (Container : Variables_Info;
      Process   : not null access procedure (Position : Cursor));

   function Iterate
       (Container : Variables_Info)
        return Name_Ordered_Iterator_Interfaces.Forward_Iterator'Class;

private

   type Var_Info is record
      Name : Unbounded_String;
      Id   : Entity_Id;
   end record;
   --  Variables are stored in alphabetical order. Keep the entity id in case
   --  there are several variables with the same name.

   function "<" (X, Y : Var_Info) return Boolean is
     (X.Name < Y.Name or else (X.Name = Y.Name and then X.Id < Y.Id));
   function "=" (X, Y : Var_Info) return Boolean is (X.Id = Y.Id);

   package Var_Lists is new Ada.Containers.Ordered_Sets (Var_Info);

   package Entity_Infos is
     new Ada.Containers.Ordered_Maps
       (Key_Type     => Entity_Id,
        Element_Type => Info,
        "="          => "=");

   type Variables_Info is tagged record
      Variables_Order : Var_Lists.Set;
      --  Vector of variable entities in the order in that variables should be
      --  displayed.

      Variables_Map : Entity_Infos.Map;
      --  Map from variable entities to information about these variables.
      --  This includes values of variables, informations about possible
      --  record fields and informations about possible attributes.
   end record;

   type Cursor is record
      S_Cursor : Var_Lists.Cursor;
   end record;

   type Cursor_Access is access all Cursor;

   type Variables_Info_Access is access all Variables_Info;

   type Iterator is new Name_Ordered_Iterator_Interfaces.Forward_Iterator with
      record
         Container : Variables_Info_Access;
         Position  : Cursor_Access;
      end record;
   --  Type that will be used for the interface to Iterator module. This is
   --  *very* inspired from the container code.

   overriding function First (Object : Iterator) return Cursor;

   overriding function Next
     (Object   : Iterator;
      Position : Cursor) return Cursor;

end Name_Ordered_Entities;
