------------------------------------------------------------------------------
--                                                                          --
--                         GNAT LIBRARY COMPONENTS                          --
--                                                                          --
--       A D A . C O N T A I N E R S . B O U N D E D _ V E C T O R S        --
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
with Ada.Containers;
use Ada.Containers;

generic
   type Index_Type is range <>;
   type Element_Type is private;

   with function "=" (Left, Right : Element_Type) return Boolean is <>;

package Verified_Vectors is
   --pragma Pure;

   subtype Extended_Index is Index_Type'Base
     range Index_Type'First - 1 ..
           Index_Type'Min (Index_Type'Base'Last - 1, Index_Type'Last) + 1;

   --  ??? i don't think we can do this...
   --  TODO: we need the ARG to either figure out how to declare this subtype,
   --  or eliminate the requirement that it be present.
   --  subtype Capacity_Subtype is Count_Type -- correct name???
   --  range 0 .. Count_Type'Max (0,
   --                             Index_Type'Pos (Index_Type'Last) -
   --                             Index_Type'Pos (Index_Type'First) + 1);
   --
   --  so for now:
   subtype Capacity_Subtype is Count_Type;

   No_Index : constant Extended_Index := Extended_Index'First;

   type Vector (Capacity : Capacity_Subtype) is tagged private;
   --pragma Preelaborable_Initialization (Vector);

   type Cursor is private;
   pragma Preelaborable_Initialization (Cursor);

   Empty_Vector : constant Vector;

   No_Element : constant Cursor;

   function "=" (Left, Right : Vector) return Boolean;

   function To_Vector (Length : Capacity_Subtype) return Vector;

   function To_Vector
     (New_Item : Element_Type;
      Length   : Capacity_Subtype) return Vector;

   function "&" (Left, Right : Vector) return Vector;

   function "&" (Left : Vector; Right : Element_Type) return Vector;

   function "&" (Left : Element_Type; Right : Vector) return Vector;

   function "&" (Left, Right : Element_Type) return Vector;

   function Capacity (Container : Vector) return Capacity_Subtype;

   procedure Reserve_Capacity
     (Container : in out Vector;
      Capacity  : Capacity_Subtype);

   function Length (Container : Vector) return Capacity_Subtype;

   procedure Set_Length
     (Container : in out Vector;
      Length    : Capacity_Subtype);

   function Is_Empty (Container : Vector) return Boolean;

   procedure Clear (Container : in out Vector);

   procedure Assign (Target : in out Vector; Source : Vector);

   function Copy
     (Source   : Vector;
      Capacity : Capacity_Subtype := 0) return Vector;

   function To_Cursor
     (Container : Vector;
      Index     : Extended_Index) return Cursor;

   function To_Index (Position : Cursor) return Extended_Index;

   function Element
     (Container : Vector;
      Index     : Index_Type) return Element_Type;

   function Element (Container : Vector; Position : Cursor) return Element_Type;

   procedure Replace_Element
     (Container : in out Vector;
      Index     : Index_Type;
      New_Item  : Element_Type);

   procedure Replace_Element
     (Container : in out Vector;
      Position  : Cursor;
      New_Item  : Element_Type);

   procedure Query_Element
     (Container : Vector;
      Index     : Index_Type;
      Process   : not null access procedure (Element : Element_Type));

   procedure Query_Element
     (Container : Vector;
      Position : Cursor;
      Process  : not null access procedure (Element : Element_Type));

   procedure Update_Element
     (Container : in out Vector;
      Index     : Index_Type;
      Process   : not null access procedure (Element : in out Element_Type));

   procedure Update_Element
     (Container : in out Vector;
      Position  : Cursor;
      Process   : not null access procedure (Element : in out Element_Type));

   procedure Move (Target : in out Vector; Source : in out Vector);

   procedure Insert
     (Container : in out Vector;
      Before    : Extended_Index;
      New_Item  : Vector);

   procedure Insert
     (Container : in out Vector;
      Before    : Cursor;
      New_Item  : Vector);

   procedure Insert
     (Container : in out Vector;
      Before    : Cursor;
      New_Item  : Vector;
      Position  : out Cursor);

   procedure Insert
     (Container : in out Vector;
      Before    : Extended_Index;
      New_Item  : Element_Type;
      Count     : Count_Type := 1);

   procedure Insert
     (Container : in out Vector;
      Before    : Cursor;
      New_Item  : Element_Type;
      Count     : Count_Type := 1);

   procedure Insert
     (Container : in out Vector;
      Before    : Cursor;
      New_Item  : Element_Type;
      Position  : out Cursor;
      Count     : Count_Type := 1);

   procedure Insert
     (Container : in out Vector;
      Before    : Extended_Index;
      Count     : Count_Type := 1);

   procedure Insert
     (Container : in out Vector;
      Before    : Cursor;
      Position  : out Cursor;
      Count     : Count_Type := 1);

   procedure Prepend
     (Container : in out Vector;
      New_Item  : Vector);

   procedure Prepend
     (Container : in out Vector;
      New_Item  : Element_Type;
      Count     : Count_Type := 1);

   procedure Append
     (Container : in out Vector;
      New_Item  : Vector);

   procedure Append
     (Container : in out Vector;
      New_Item  : Element_Type;
      Count     : Count_Type := 1);

   procedure Insert_Space
     (Container : in out Vector;
      Before    : Extended_Index;
      Count     : Count_Type := 1);

   procedure Insert_Space
     (Container : in out Vector;
      Before    : Cursor;
      Position  : out Cursor;
      Count     : Count_Type := 1);

   procedure Delete
     (Container : in out Vector;
      Index     : Extended_Index;
      Count     : Count_Type := 1);

   procedure Delete
     (Container : in out Vector;
      Position  : in out Cursor;
      Count     : Count_Type := 1);

   procedure Delete_First
     (Container : in out Vector;
      Count     : Count_Type := 1);

   procedure Delete_Last
     (Container : in out Vector;
      Count     : Count_Type := 1);

   procedure Reverse_Elements (Container : in out Vector);

   procedure Swap (Container : in out Vector; I, J : Index_Type);

   procedure Swap (Container : in out Vector; I, J : Cursor);

   function First_Index (Container : Vector) return Index_Type;

   function First (Container : Vector) return Cursor;

   function First_Element (Container : Vector) return Element_Type;

   function Last_Index (Container : Vector) return Extended_Index;

   function Last (Container : Vector) return Cursor;

   function Last_Element (Container : Vector) return Element_Type;

   function Next (Container : Vector; Position : Cursor) return Cursor;

   procedure Next (Container : Vector; Position : in out Cursor);

   function Previous (Container : Vector; Position : Cursor) return Cursor;

   procedure Previous (Container : Vector; Position : in out Cursor);

   function Find_Index
     (Container : Vector;
      Item      : Element_Type;
      Index     : Index_Type := Index_Type'First) return Extended_Index;

   function Find
     (Container : Vector;
      Item      : Element_Type;
      Position  : Cursor := No_Element) return Cursor;

   function Reverse_Find_Index
     (Container : Vector;
      Item      : Element_Type;
      Index     : Index_Type := Index_Type'Last) return Extended_Index;

   function Reverse_Find
     (Container : Vector;
      Item      : Element_Type;
      Position  : Cursor := No_Element) return Cursor;

   function Contains
     (Container : Vector;
      Item      : Element_Type) return Boolean;

   function Has_Element (Container : Vector; Position : Cursor) return Boolean;

   procedure Iterate
     (Container : Vector;
      Process   : not null access procedure (Container : Vector; Position : Cursor));

   procedure Reverse_Iterate
     (Container : Vector;
      Process   : not null access procedure (Container : Vector; Position : Cursor));

   generic
      with function "<" (Left, Right : Element_Type) return Boolean is <>;
   package Generic_Sorting is

      function Is_Sorted (Container : Vector) return Boolean;

      procedure Sort (Container : in out Vector);

      procedure Merge (Target : in out Vector; Source : in out Vector);

   end Generic_Sorting;

   function Left (Container : Vector; Position : Cursor) return Vector;

   function Right (Container : Vector; Position : Cursor) return Vector;

private

   pragma Inline (First_Index);
   pragma Inline (Last_Index);
   pragma Inline (Element);
   pragma Inline (First_Element);
   pragma Inline (Last_Element);
   pragma Inline (Query_Element);
   pragma Inline (Update_Element);
   pragma Inline (Replace_Element);
   pragma Inline (Contains);
   pragma Inline (Next);
   pragma Inline (Previous);

   type Elements_Array is array (Count_Type range <>) of Element_Type;
   function "=" (L, R : Elements_Array) return Boolean is abstract;

   type Plain_Vector (Capacity : Capacity_Subtype) is record
      Elements : Elements_Array (1 .. Capacity);
      Last     : Extended_Index := No_Index;
      Busy     : Natural := 0;
      Lock     : Natural := 0;
   end record;

   type Plain_Access is access all Plain_Vector;

   type Kind is (Plain, Part);

   type Vector (Capacity : Capacity_Subtype) is tagged record
      Plain : Plain_Access := new Plain_Vector (Capacity);
      K : Kind := Verified_Vectors.Plain;
      First : Count_Type := 0;
      Last : Index_Type'Base := No_Index;
   end record;

   use Ada.Streams;

   procedure Write
     (Stream    : not null access Root_Stream_Type'Class;
      Container : Vector);

   for Vector'Write use Write;

   procedure Read
     (Stream    : not null access Root_Stream_Type'Class;
      Container : out Vector);

   for Vector'Read use Read;

   type Cursor is record
      Valid : Boolean := True;
      Index     : Index_Type := Index_Type'First;
   end record;

   procedure Write
     (Stream   : not null access Root_Stream_Type'Class;
      Position : Cursor);

   for Cursor'Write use Write;

   procedure Read
     (Stream   : not null access Root_Stream_Type'Class;
      Position : out Cursor);

   for Cursor'Read use Read;

   Empty_Vector : constant Vector := (Capacity => 0, others => <>);

   No_Element : constant Cursor := (Valid => False, Index => Index_Type'First);

end Verified_Vectors;
