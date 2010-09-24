------------------------------------------------------------------------------
--                                                                          --
--                         GNAT LIBRARY COMPONENTS                          --
--                                                                          --
--                       A D A . C O N T A I N E R S .                      --
--       H A S H _ T A B L E S . G E N E R I C _ O P E R A T I O N S        --
--                                                                          --
--                                 S p e c                                  --
--                                                                          --
--          Copyright (C) 2004-2007, Free Software Foundation, Inc.         --
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

--  Hash_Table_Type is used to implement hashed containers. This package
--  declares hash-table operations that do not depend on keys.

with Ada.Streams;

generic

   with package HT_Types is
     new Generic_Hash_Table_Types (<>);
   --  we should fix this to either pass in the type too, or just
   --  rewrite the ops below to accept HT'Class  ???

   use HT_Types;

   with function Hash_Node
     (HT   : Hash_Table_Type;
      Node : Node_Access) return Hash_Type;

   with function Get_Next
     (HT   : Hash_Table_Type;
      Node : Node_Access) return Node_Access;

   with procedure Set_Next
     (HT   : in out Hash_Table_Type;
      Node : Node_Access;
      Next : Node_Access);

   with procedure Set_Has_Element
     (HT   : in out Hash_Table_Type;
      Node : Node_Access;
      Has_Element : Boolean);

package Verified_Hash_Tables.Generic_Operations is
   --pragma Pure;

--  ???
--     procedure Free_Hash_Table (Buckets : in out Buckets_Access);
   --  First frees the nodes in all non-null buckets of Buckets, and then frees
   --  the Buckets array itself.

--  ???
--     function Index
--       (Buckets : Buckets_Type;
--        Node    : Node_Access) return Count_Type;
--     pragma Inline (Index);
   --  Uses the hash value of Node to compute its Buckets array index

   function Index
     (HT   : Hash_Table_Type;
      Node : Node_Access) return Hash_Type;
   pragma Inline (Index);
   --  Uses the hash value of Node to compute its Hash_Table buckets array
   --  index.

   generic
      with function Find
        (HT  : Hash_Table_Type;
         Key : Node_Access) return Boolean;
   function Generic_Equal
     (L, R : Hash_Table_Type) return Boolean;
   --  Used to implement hashed container equality. For each node in hash table
   --  L, it calls Find to search for an equivalent item in hash table R. If
   --  Find returns False for any node then Generic_Equal terminates
   --  immediately and returns False. Otherwise if Find returns True for every
   --  node then Generic_Equal returns True.

   procedure Clear (HT : in out Hash_Table_Type);
   --  Deallocates each node in hash table HT. (Note that it only deallocates
   --  the nodes, not the buckets array.)  Program_Error is raised if the hash
   --  table is busy.

--  ???
--     procedure Move (Target, Source : in out Hash_Table_Type);
   --  Moves (not copies) the buckets array and nodes from Source to
   --  Target. Program_Error is raised if Source is busy. The Target is first
   --  cleared to deallocate its nodes (implying that Program_Error is also
   --  raised if Target is busy). Source is empty following the move.

--  ???
--     function Capacity (HT : Hash_Table_Type) return Count_Type;
   --  Returns the length of the buckets array

   procedure Reserve_Capacity
     (HT : Hash_Table_Type;
      N  : Count_Type);
   --  this desc is incorrect ???
   --  If N is greater than the current capacity, then it expands the buckets
   --  array to at least the value N. If N is less than the current capacity,
   --  then it contracts the buckets array. In either case existing nodes are
   --  rehashed onto the new buckets array, and the old buckets array is
   --  deallocated. Program_Error is raised if the hash table is busy.

   procedure Delete_Node_Sans_Free
     (HT : in out Hash_Table_Type;
      X  : Node_Access);
   --  Removes node X from the hash table without deallocating the node

   function First (HT : Hash_Table_Type) return Node_Access;
   --  Returns the head of the list in the first (lowest-index) non-empty
   --  bucket.

   function Next
     (HT   : Hash_Table_Type;
      Node : Node_Access) return Node_Access;
   --  Returns the node that immediately follows Node. This corresponds to
   --  either the next node in the same bucket, or (if Node is the last node in
   --  its bucket) the head of the list in the first non-empty bucket that
   --  follows.

   generic
      with procedure Process (Node : Node_Access);
   procedure Generic_Iteration (HT : Hash_Table_Type);
   --  Calls Process for each node in hash table HT

   generic
      use Ada.Streams;
      with procedure Write
        (Stream : not null access Root_Stream_Type'Class;
         Node   : Node_Access);
   procedure Generic_Write
     (Stream : not null access Root_Stream_Type'Class;
      HT     : Hash_Table_Type);
   --  Used to implement the streaming attribute for hashed containers. It
   --  calls Write for each node to write its value into Stream.

   generic
      with procedure Allocate_Node
        (HT : in out Hash_Table_Type;
         X  : out Node_Access);
      use Ada.Streams;
   procedure Generic_Read
     (Stream : not null access Root_Stream_Type'Class;
      HT     : out Hash_Table_Type);
   --  Used to implement the streaming attribute for hashed containers. It
   --  first clears hash table HT, then populates the hash table by calling
   --  New_Node for each item in Stream.

--  ???
--     function New_Buckets (Length : Hash_Type) return Buckets_Access;
--     pragma Inline (New_Buckets);
   --  Allocate a new Buckets_Type array with bounds 0..Length-1.

--  ???
--     procedure Free_Buckets (Buckets : in out Buckets_Access);
--     pragma Inline (Free_Buckets);
   --  Unchecked_Deallocate Buckets.

   --  Note: New_Buckets and Free_Buckets are needed because Buckets_Access has
   --  an empty pool.

   procedure Free
     (HT : in out Hash_Table_Type;
      X  : in out Count_Type);

   generic
      with procedure Initialize_Node (Node : in out Node_Type);
   procedure Generic_Allocate_Node
     (HT : in out Hash_Table_Type;
      X  : out Count_Type);

   function Default_Modulus (Capacity : Count_Type) return Hash_Type;
   pragma Inline (Default_Modulus);

   function Vet (HT : Hash_Table_Type; Node : Node_Access) return Boolean;

end Verified_Hash_Tables.Generic_Operations;
