------------------------------------------------------------------------------
--                                                                          --
--                         GNAT LIBRARY COMPONENTS                          --
--                                                                          --
--   A D A . C O N T A I N E R S . B O U N D E D _ H A S H E D _ S E T S    --
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

private with Verified_Hash_Tables;  -- ???
private with Ada.Streams;

with Ada.Containers;
use Ada.Containers;

generic
   type Element_Type is private;

   with function Hash (Element : Element_Type) return Hash_Type;

   with function Equivalent_Elements (Left, Right : Element_Type)
                                     return Boolean;

   with function "=" (Left, Right : Element_Type) return Boolean is <>;

package Verified_Hashed_Sets is
   --pragma Pure;

   type Set (Capacity : Count_Type; Modulus : Hash_Type) is tagged private;
   --pragma Preelaborable_Initialization (Set);

   type Cursor is private;
   pragma Preelaborable_Initialization (Cursor);

   Empty_Set : constant Set;

   No_Element : constant Cursor;

   function "=" (Left, Right : Set) return Boolean;

   function Equivalent_Sets (Left, Right : Set) return Boolean;

   function To_Set (New_Item : Element_Type) return Set;

   function Capacity (Container : Set) return Count_Type;

   procedure Reserve_Capacity
     (Container : in out Set;
      Capacity  : Count_Type);

   function Length (Container : Set) return Count_Type;

   function Is_Empty (Container : Set) return Boolean;

   procedure Clear (Container : in out Set);

   procedure Assign (Target : in out Set; Source : Set);

   function Copy (Source   : Set;
                  Capacity : Count_Type := 0) return Set;

   function Element (Container : Set; Position : Cursor) return Element_Type;

   procedure Replace_Element
     (Container : in out Set;
      Position  : Cursor;
      New_Item  : Element_Type);

   procedure Query_Element
     (Container : in out Set;
      Position : Cursor;
      Process  : not null access procedure (Element : Element_Type));

   procedure Move (Target : in out Set; Source : in out Set);

   procedure Insert
     (Container : in out Set;
      New_Item  : Element_Type;
      Position  : out Cursor;
      Inserted  : out Boolean);

   procedure Insert  (Container : in out Set; New_Item : Element_Type);

   procedure Include (Container : in out Set; New_Item : Element_Type);

   procedure Replace (Container : in out Set; New_Item : Element_Type);

   procedure Exclude (Container : in out Set; Item     : Element_Type);

   procedure Delete  (Container : in out Set; Item     : Element_Type);

   procedure Delete (Container : in out Set; Position  : in out Cursor);

   procedure Union (Target : in out Set; Source : Set);

   function Union (Left, Right : Set) return Set;

   function "or" (Left, Right : Set) return Set renames Union;

   procedure Intersection (Target : in out Set; Source : Set);

   function Intersection (Left, Right : Set) return Set;

   function "and" (Left, Right : Set) return Set renames Intersection;

   procedure Difference (Target : in out Set; Source : Set);

   function Difference (Left, Right : Set) return Set;

   function "-" (Left, Right : Set) return Set renames Difference;

   procedure Symmetric_Difference (Target : in out Set; Source : Set);

   function Symmetric_Difference (Left, Right : Set) return Set;

   function "xor" (Left, Right : Set) return Set
     renames Symmetric_Difference;

   function Overlap (Left, Right : Set) return Boolean;

   function Is_Subset (Subset : Set; Of_Set : Set) return Boolean;

   function First (Container : Set) return Cursor;

   function Next (Container : Set; Position : Cursor) return Cursor;

   procedure Next (Container : Set; Position : in out Cursor);

   function Find
     (Container : Set;
      Item      : Element_Type) return Cursor;

   function Contains (Container : Set; Item : Element_Type) return Boolean;

   function Has_Element (Container : Set; Position : Cursor) return Boolean;

   function Equivalent_Elements (Left : Set; CLeft : Cursor;
                                 Right : Set; CRight : Cursor) return Boolean;

   function Equivalent_Elements
     (Left  : Set; CLeft : Cursor;
      Right : Element_Type) return Boolean;

   function Equivalent_Elements
     (Left  : Element_Type;
      Right : Set; CRight : Cursor) return Boolean;

   procedure Iterate
     (Container : Set;
      Process   : not null access procedure (Container : Set; Position : Cursor));

   function Default_Modulus (Capacity : Count_Type) return Hash_Type;

   generic
      type Key_Type (<>) is private;

      with function Key (Element : Element_Type) return Key_Type;

      with function Hash (Key : Key_Type) return Hash_Type;

      with function Equivalent_Keys (Left, Right : Key_Type) return Boolean;

   package Generic_Keys is

      function Key (Container : Set; Position : Cursor) return Key_Type;

      function Element (Container : Set; Key : Key_Type) return Element_Type;

      procedure Replace
        (Container : in out Set;
         Key       : Key_Type;
         New_Item  : Element_Type);

      procedure Exclude (Container : in out Set; Key : Key_Type);

      procedure Delete (Container : in out Set; Key : Key_Type);

      function Find (Container : Set; Key : Key_Type) return Cursor;

      function Contains (Container : Set; Key : Key_Type) return Boolean;

      procedure Update_Element_Preserving_Key
        (Container : in out Set;
         Position  : Cursor;
         Process   : not null access
                       procedure (Element : in out Element_Type));

   end Generic_Keys;

   function Strict_Equal (Left, Right : Set) return Boolean;

   function Left (Container : Set; Position : Cursor) return Set;

   function Right (Container : Set; Position : Cursor) return Set;

private

   pragma Inline (Next);

   type Node_Type is
      record
         Element : Element_Type;
         Next    : Count_Type;
         Has_Element : Boolean := False;
      end record;

   package HT_Types is new Verified_Hash_Tables.Generic_Hash_Table_Types
     (Node_Type);

   type HT_Access is access all HT_Types.Hash_Table_Type;

   type Kind is (Plain, Part);

   type Set (Capacity : Count_Type; Modulus : Hash_Type) is tagged record
      HT : HT_Access := new HT_Types.Hash_Table_Type'(Capacity, Modulus, others => <>);
      K : Kind := Plain;
      Length : Count_Type := 0;
      First : Count_Type := 0;
      Last : Count_Type := 0;
   end record;

   use HT_Types;
   use Ada.Streams;

   type Cursor is
      record
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
      Container : Set);

   for Set'Write use Write;

   procedure Read
     (Stream    : not null access Root_Stream_Type'Class;
      Container : out Set);

   for Set'Read use Read;

   Empty_Set : constant Set := (Capacity => 0, Modulus => 0, others => <>);

end Verified_Hashed_Sets;
