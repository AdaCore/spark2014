------------------------------------------------------------------------------
--                                                                          --
--                         GNAT LIBRARY COMPONENTS                          --
--                                                                          --
--    A D A . C O N T A I N E R S . F O R M A L _ H A S H E D _ M A P S     --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--          Copyright (C) 2004-2010, Free Software Foundation, Inc.         --
--                                                                          --
-- This specification is derived from the Ada Reference Manual for use with --
-- GNAT. The copyright notice above, and the license provisions that follow --
-- apply solely to the  contents of the part following the private keyword. --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
-- OUT ANY WARRANTY;  without even the  implied warranty of MERCHANTABILITY --
-- or FITNESS FOR A PARTICULAR PURPOSE.                                     --
--                                                                          --
-- As a special exception under Section 7 of GPL version 3, you are granted --
-- additional permissions described in the GCC Runtime Library Exception,   --
-- version 3.1, as published by the Free Software Foundation.               --
--                                                                          --
-- You should have received a copy of the GNU General Public License and    --
-- a copy of the GCC Runtime Library Exception along with this program;     --
-- see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see    --
-- <http://www.gnu.org/licenses/>.                                          --
------------------------------------------------------------------------------

--  This spec is derived from package Ada.Containers.Bounded_Hashed_Maps in the
--  Ada 2012 RM. The modifications are to facilitate formal proofs by making it
--  easier to express properties.

--  The modifications are:

--    A parameter for the container is added to every function reading the
--    contents of a container: Key, Element, Next, Query_Element, Has_Element,
--    Iterate, Equivalent_Keys. This change is motivated by the need to have
--    cursors which are valid on different containers (typically a container C
--    and its previous version C'Old) for expressing properties, which is not
--    possible if cursors encapsulate an access to the underlying container.

--    There are four new functions:

--      function Strict_Equal (Left, Right : Map) return Boolean;
--      function Overlap (Left, Right : Map) return Boolean;
--      function Left  (Container : Map; Position : Cursor) return Map;
--      function Right (Container : Map; Position : Cursor) return Map;

--    See detailed specifications for these subprograms

private with Ada.Containers.Hash_Tables;
private with Ada.Streams;

generic
   type Key_Type is private;
   type Element_Type is private;

   with function Hash (Key : Key_Type) return Hash_Type;
   with function Equivalent_Keys (Left, Right : Key_Type) return Boolean;
   with function "=" (Left, Right : Element_Type) return Boolean is <>;

package Ada.Containers.Formal_Hashed_Maps is
   pragma Pure;

   type Map (Capacity : Count_Type; Modulus : Hash_Type) is tagged private;
   pragma Preelaborable_Initialization (Map);

   type Cursor is private;
   pragma Preelaborable_Initialization (Cursor);

   Empty_Map : constant Map;

   No_Element : constant Cursor;

   function "=" (Left, Right : Map) return Boolean;

   function Capacity (Container : Map) return Count_Type;

   procedure Reserve_Capacity
     (Container : in out Map;
      Capacity  : Count_Type);

   function Length (Container : Map) return Count_Type;

   function Is_Empty (Container : Map) return Boolean;

   --  ??? what does clear do to active elements?
   procedure Clear (Container : in out Map);

   procedure Assign (Target : in out Map; Source : Map);

   --  ???
   --  capacity=0 means use container.length as cap of tgt
   --  modulos=0 means use default_modulous(container.length)
   function Copy
     (Source   : Map;
      Capacity : Count_Type := 0) return Map;

   function Key (Container : Map; Position : Cursor) return Key_Type;

   function Element (Container : Map; Position : Cursor) return Element_Type;

   procedure Replace_Element
     (Container : in out Map;
      Position  : Cursor;
      New_Item  : Element_Type);

   procedure Query_Element
     (Container : in out Map;
      Position  : Cursor;
      Process   : not null access
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

   function First (Container : Map) return Cursor;

   function Next (Container : Map; Position : Cursor) return Cursor;

   procedure Next (Container : Map; Position : in out Cursor);

   function Find (Container : Map; Key : Key_Type) return Cursor;

   function Contains (Container : Map; Key : Key_Type) return Boolean;

   function Element (Container : Map; Key : Key_Type) return Element_Type;

   function Has_Element (Container : Map; Position : Cursor) return Boolean;

   function Equivalent_Keys
     (Left   : Map;
      CLeft  : Cursor;
      Right  : Map;
      CRight : Cursor) return Boolean;

   function Equivalent_Keys
     (Left  : Map;
      CLeft : Cursor;
      Right : Key_Type) return Boolean;

   function Equivalent_Keys
     (Left   : Key_Type;
      Right  : Map;
      CRight : Cursor) return Boolean;

   procedure Iterate
     (Container : Map;
      Process   : not null access
                    procedure (Container : Map; Position : Cursor));

   function Default_Modulus (Capacity : Count_Type) return Hash_Type;

   function Strict_Equal (Left, Right : Map) return Boolean;
   --  Strict_Equal returns True if the containers are physically equal, i.e.
   --  they are structurally equal (function "=" returns True) and that they
   --  have the same set of cursors.

   function Left  (Container : Map; Position : Cursor) return Map;
   function Right (Container : Map; Position : Cursor) return Map;
   --  Left returns a container containing all elements preceding Position
   --  (excluded) in Container. Right returns a container containing all
   --  elements following Position (included) in Container. These two new
   --  functions can be used to express invariant properties in loops which
   --  iterate over containers. Left returns the part of the container already
   --  scanned and Right the part not scanned yet.

   function Overlap (Left, Right : Map) return Boolean;
   --  Overlap returns True if the containers have common keys

private
   pragma Inline (Length);
   pragma Inline (Is_Empty);
   pragma Inline (Clear);
   pragma Inline (Key);
   pragma Inline (Element);
   pragma Inline (Contains);
   pragma Inline (Capacity);
   pragma Inline (Has_Element);
   pragma Inline (Equivalent_Keys);
   pragma Inline (Next);

   type Node_Type is record
      Key         : Key_Type;
      Element     : Element_Type;
      Next        : Count_Type;
      Has_Element : Boolean := False;
   end record;

   package HT_Types is new
     Ada.Containers.Hash_Tables.Generic_Bounded_Hash_Table_Types
       (Node_Type);

   type Map (Capacity : Count_Type; Modulus : Hash_Type) is
      new HT_Types.Hash_Table_Type (Capacity, Modulus) with null record;

   use HT_Types;
   use Ada.Streams;

   procedure Write
     (Stream    : not null access Root_Stream_Type'Class;
      Container : Map);

   for Map'Write use Write;

   procedure Read
     (Stream    : not null access Root_Stream_Type'Class;
      Container : out Map);

   for Map'Read use Read;

   type Map_Access is access all Map;
   for Map_Access'Storage_Size use 0;

   type Cursor is record
      Node : Count_Type;
   end record;

   procedure Read
     (Stream : not null access Root_Stream_Type'Class;
      Item   : out Cursor);

   for Cursor'Read use Read;

   procedure Write
     (Stream : not null access Root_Stream_Type'Class;
      Item   : Cursor);

   for Cursor'Write use Write;

   Empty_Map : constant Map := (Capacity => 0, Modulus => 0, others => <>);

   No_Element : constant Cursor := (Node => 0);

end Ada.Containers.Formal_Hashed_Maps;
