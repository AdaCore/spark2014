------------------------------------------------------------------------------
--                                                                          --
--                         GNAT LIBRARY COMPONENTS                          --
--                                                                          --
--  A D A . C O N T A I N E R S . B O U N D E D _ O R D E R E D _ M A P S   --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--          Copyright (C) 2004-2008, Free Software Foundation, Inc.         --
--                                                                          --
-- This specification is derived from the Ada Reference Manual for use with --
-- GNAT. The copyright notice above, and the license provisions that follow --
-- apply solely to the  contents of the part following the private keyword. --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 2,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License --
-- for  more details.  You should have  received  a copy of the GNU General --
-- Public License  distributed with GNAT;  see file COPYING.  If not, write --
-- to  the  Free Software Foundation,  51  Franklin  Street,  Fifth  Floor, --
-- Boston, MA 02110-1301, USA.                                              --
--                                                                          --
-- As a special exception,  if other files  instantiate  generics from this --
-- unit, or you link  this unit with other files  to produce an executable, --
-- this  unit  does not  by itself cause  the resulting  executable  to  be --
-- covered  by the  GNU  General  Public  License.  This exception does not --
-- however invalidate  any other reasons why  the executable file  might be --
-- covered by the  GNU Public License.                                      --
--                                                                          --
-- This unit was originally developed by Matthew J Heaney.                  --
------------------------------------------------------------------------------

private with Bounded_Red_Black_Trees;
private with Ada.Streams;
with Ada.Containers; use Ada.Containers;

generic
   type Key_Type is private;
   type Element_Type is private;

   with function "<" (Left, Right : Key_Type) return Boolean is <>;
   with function "=" (Left, Right : Element_Type) return Boolean is <>;

package Verified_Ordered_Maps is
   pragma Pure;

   function Equivalent_Keys (Left, Right : Key_Type) return Boolean;

   type Map (Capacity : Count_Type) is tagged private;
   --pragma Preelaborable_Initialization (Map);

   type Cursor is private;
   pragma Preelaborable_Initialization (Cursor);

   Empty_Map : constant Map;

   No_Element : constant Cursor;

   function "=" (Left, Right : Map) return Boolean;

   function Length (Container : Map) return Count_Type;

   function Is_Empty (Container : Map) return Boolean;

   procedure Clear (Container : in out Map);

   procedure Assign (Target : in out Map; Source : Map);

   function Copy (Source : Map; Capacity : Count_Type := 0) return Map;

   function Key (Container : Map; Position : Cursor) return Key_Type;

   function Element (Container : Map; Position : Cursor) return Element_Type;

   procedure Replace_Element
     (Container : in out Map;
      Position  : Cursor;
      New_Item  : Element_Type);

   procedure Query_Element
     (Container : in out Map;
      Position : Cursor;
      Process  : not null access
                   procedure (Key : Key_Type; Element : Element_Type));

   procedure Update_Element
     (Container : in out Map;
      Position  : Cursor;
      Process   : not null access
                   procedure (Key : Key_Type; Element : in out Element_Type));

   procedure Move (Target : in out Map; Source : in out Map);

   procedure Insert
     (Container : in out Map;
      Key       : Key_Type;
      New_Item  : Element_Type;
      Position  : out Cursor;
      Inserted  : out Boolean);

   procedure Insert
     (Container : in out Map;
      Key       : Key_Type;
      Position  : out Cursor;
      Inserted  : out Boolean);

   procedure Insert
     (Container : in out Map;
      Key       : Key_Type;
      New_Item  : Element_Type);

   procedure Include
     (Container : in out Map;
      Key       : Key_Type;
      New_Item  : Element_Type);

   procedure Replace
     (Container : in out Map;
      Key       : Key_Type;
      New_Item  : Element_Type);

   procedure Exclude (Container : in out Map; Key : Key_Type);

   procedure Delete (Container : in out Map; Key : Key_Type);

   procedure Delete (Container : in out Map; Position : in out Cursor);

   procedure Delete_First (Container : in out Map);

   procedure Delete_Last (Container : in out Map);

   function First (Container : Map) return Cursor;

   function First_Element (Container : Map) return Element_Type;

   function First_Key (Container : Map) return Key_Type;

   function Last (Container : Map) return Cursor;

   function Last_Element (Container : Map) return Element_Type;

   function Last_Key (Container : Map) return Key_Type;

   function Next (Container : Map; Position : Cursor) return Cursor;

   procedure Next (Container : Map; Position : in out Cursor);

   function Previous (Container : Map; Position : Cursor) return Cursor;

   procedure Previous (Container : Map; Position : in out Cursor);

   function Find (Container : Map; Key : Key_Type) return Cursor;

   function Element (Container : Map; Key : Key_Type) return Element_Type;

   function Floor (Container : Map; Key : Key_Type) return Cursor;

   function Ceiling (Container : Map; Key : Key_Type) return Cursor;

   function Contains (Container : Map; Key : Key_Type) return Boolean;

   function Has_Element (Container : Map; Position : Cursor) return Boolean;

   procedure Iterate
     (Container : Map;
      Process   : not null access procedure (Container : Map; Position : Cursor));

   procedure Reverse_Iterate
     (Container : Map;
      Process   : not null access procedure (Container : Map; Position : Cursor));

   function Strict_Equal (Left, Right : Map) return Boolean;

   function Left (Container : Map; Position : Cursor) return Map;

   function Right (Container : Map; Position : Cursor) return Map;

   function Overlap (Left, Right : Map) return Boolean;

private

   pragma Inline (Next);
   pragma Inline (Previous);

   subtype Node_Access is Count_Type;

   use Bounded_Red_Black_Trees;

   type Node_Type is record
      Parent  : Node_Access'Base := -1;
      Left    : Node_Access;
      Right   : Node_Access;
      Color   : Bounded_Red_Black_Trees.Color_Type := Red;
      Key     : Key_Type;
      Element : Element_Type;
   end record;

   type Nodes_Type is array (Count_Type range <>) of Node_Type;

   type Kind is (Plain, Part);

   type Tree_Type (Capacity : Count_Type) is
     new Bounded_Red_Black_Trees.Tree_Type with record
        Free  : Count_Type := 0;
        Nodes : Nodes_Type (1 .. Capacity);
   end record;

   type Tree_Type_Access is access all Tree_Type;

   type Map (Capacity : Count_Type) is tagged record
      Tree : Tree_Type_Access := new Tree_Type'(Capacity, others => <>);
      K : Kind := Plain;
      Length : Count_Type := 0;
      First : Count_Type := 0;
      Last : Count_Type := 0;
   end record;

   use Ada.Streams;

   type Map_Access is access all Map;
   for Map_Access'Storage_Size use 0;

   type Cursor is record
      Node      : Node_Access;
   end record;

   procedure Write
     (Stream : not null access Root_Stream_Type'Class;
      Item   : Cursor);

   for Cursor'Write use Write;

   procedure Read
     (Stream : not null access Root_Stream_Type'Class;
      Item   : out Cursor);

   for Cursor'Read use Read;

   No_Element : constant Cursor := (Node => 0);

   procedure Write
     (Stream    : not null access Root_Stream_Type'Class;
      Container : Map);

   for Map'Write use Write;

   procedure Read
     (Stream    : not null access Root_Stream_Type'Class;
      Container : out Map);

   for Map'Read use Read;

   Empty_Map : constant Map := (Capacity => 0, others => <>);

end Verified_Ordered_Maps;
