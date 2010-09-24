------------------------------------------------------------------------------
--                                                                          --
--                         GNAT LIBRARY COMPONENTS                          --
--                                                                          --
--                 ADA.CONTAINERS.BOUNDED_DOUBLY_LINKED_LISTS               --
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

private with Ada.Streams;
with Ada.Containers; use Ada.Containers;

generic
   type Element_Type is private;

   with function "=" (Left, Right : Element_Type)
      return Boolean is <>;

package Verified_Doubly_Linked_Lists is
   pragma Pure;

   type List (Capacity : Count_Type) is tagged private;
   -- pragma Preelaborable_Initialization (List);

   type Cursor is private;
   pragma Preelaborable_Initialization (Cursor);

   Empty_List : constant List;

   No_Element : constant Cursor;

   function "=" (Left, Right : List) return Boolean;

   function Length (Container : List) return Count_Type;

   function Is_Empty (Container : List) return Boolean;

   procedure Clear (Container : in out List);

   procedure Assign (Target : in out List; Source : List);

   function Copy (Source : List; Capacity : Count_Type := 0) return List;

   function Element (Container : List; Position : Cursor) return Element_Type;

   procedure Replace_Element
     (Container : in out List;
      Position  : Cursor;
      New_Item  : Element_Type);

   procedure Query_Element
     (Container : List; Position : Cursor;
      Process  : not null access procedure (Element : Element_Type));

   procedure Update_Element
     (Container : in out List;
      Position  : Cursor;
      Process   : not null access procedure (Element : in out Element_Type));

   procedure Move (Target : in out List; Source : in out List);

   procedure Insert
     (Container : in out List;
      Before    : Cursor;
      New_Item  : Element_Type;
      Count     : Count_Type := 1);

   procedure Insert
     (Container : in out List;
      Before    : Cursor;
      New_Item  : Element_Type;
      Position  : out Cursor;
      Count     : Count_Type := 1);

   procedure Insert
     (Container : in out List;
      Before    : Cursor;
      Position  : out Cursor;
      Count     : Count_Type := 1);

   procedure Prepend
     (Container : in out List;
      New_Item  : Element_Type;
      Count     : Count_Type := 1);

   procedure Append
     (Container : in out List;
      New_Item  : Element_Type;
      Count     : Count_Type := 1);

   procedure Delete
     (Container : in out List;
      Position  : in out Cursor;
      Count     : Count_Type := 1);

   procedure Delete_First
     (Container : in out List;
      Count     : Count_Type := 1);

   procedure Delete_Last
     (Container : in out List;
      Count     : Count_Type := 1);

   procedure Reverse_Elements (Container : in out List);

   procedure Swap
     (Container : in out List;
      I, J      : Cursor);

   procedure Swap_Links
     (Container : in out List;
      I, J      : Cursor);

   procedure Splice
     (Target : in out List;
      Before : Cursor;
      Source : in out List);

   procedure Splice
     (Target   : in out List;
      Before   : Cursor;
      Source   : in out List;
      Position : in out Cursor);

   procedure Splice
     (Container : in out List;
      Before    : Cursor;
      Position  : Cursor);

   function First (Container : List) return Cursor;

   function First_Element (Container : List) return Element_Type;

   function Last (Container : List) return Cursor;

   function Last_Element (Container : List) return Element_Type;

   function Next (Container : List; Position : Cursor) return Cursor;

   procedure Next (Container : List; Position : in out Cursor);

   function Previous (Container : List; Position : Cursor) return Cursor;

   procedure Previous (Container : List; Position : in out Cursor);

   function Find
     (Container : List;
      Item      : Element_Type;
      Position  : Cursor := No_Element) return Cursor;

   function Reverse_Find
     (Container : List;
      Item      : Element_Type;
      Position  : Cursor := No_Element) return Cursor;

   function Contains
     (Container : List;
      Item      : Element_Type) return Boolean;

   function Has_Element (Container : List; Position : Cursor) return Boolean;

   procedure Iterate
     (Container : List;
      Process   : not null access procedure (Container : List; Position : Cursor));

   procedure Reverse_Iterate
     (Container : List;
      Process   : not null access procedure (Container : List; Position : Cursor));

   generic
      with function "<" (Left, Right : Element_Type) return Boolean is <>;
   package Generic_Sorting is

      function Is_Sorted (Container : List) return Boolean;

      procedure Sort (Container : in out List);

      procedure Merge (Target, Source : in out List);

   end Generic_Sorting;

   function Left (Container : List; Position : Cursor) return List;

   function Right (Container : List; Position : Cursor) return List;

private

   type Node_Type is record
      Prev    : Count_Type'Base := -1;
      Next    : Count_Type;
      Element : Element_Type;
   end record;
   function "=" (L, R : Node_Type) return Boolean is abstract;

   type Node_Array is array (Count_Type range <>) of Node_Type;
   function "=" (L, R : Node_Array) return Boolean is abstract;

   type List_Access is access all List;
   for List_Access'Storage_Size use 0;

   type Kind is (Part, Plain);

   type Plain_List (Capacity : Count_Type) is record
      Nodes  : Node_Array (1 .. Capacity) := (others => <>);
      Free   : Count_Type'Base := -1;
      Busy   : Natural := 0;
      Lock   : Natural := 0;
   end record;

   type PList_Access is access Plain_List;

   type Part_List is record
      LLength : Count_Type := 0;
      LFirst : Count_Type := 0;
      LLast : Count_Type := 0;
   end record;

   type List (Capacity : Count_Type) is tagged record
      K : Kind := Plain;
      Length : Count_Type := 0;
      First : Count_Type := 0;
      Last : Count_Type := 0;
      Part : Part_List;
      Plain : PList_Access := new Plain_List'(Capacity, others => <>);
   end record;

   use Ada.Streams;

   procedure Read
     (Stream : not null access Root_Stream_Type'Class;
      Item   : out List);

   for List'Read use Read;

   procedure Write
     (Stream : not null access Root_Stream_Type'Class;
      Item   : List);

   for List'Write use Write;

   type Cursor is
      record
         Node      : Count_Type := 0;
      end record;

   procedure Read
     (Stream : not null access Root_Stream_Type'Class;
      Item   : out Cursor);

   for Cursor'Read use Read;

   procedure Write
     (Stream : not null access Root_Stream_Type'Class;
      Item   : Cursor);

   for Cursor'Write use Write;

   Empty_List : constant List := (0, others => <>);

   No_Element : constant Cursor := (Node => 0);

end Verified_Doubly_Linked_Lists;
