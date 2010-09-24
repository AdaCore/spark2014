------------------------------------------------------------------------------
--                                                                          --
--                         GNAT LIBRARY COMPONENTS                          --
--                                                                          --
--                       A D A . C O N T A I N E R S .                      --
--       H A S H _ T A B L E S . G E N E R I C _ O P E R A T I O N S        --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--          Copyright (C) 2004-2008, Free Software Foundation, Inc.         --
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
with Ada.Text_IO;

with Ada.Containers.Prime_Numbers;
with System;  use type System.Address;

package body Verified_Hash_Tables.Generic_Operations is

--  ???
--     type Buckets_Allocation is access all Buckets_Type;
   --  Used for allocation and deallocation (see New_Buckets and
   --  Free_Buckets). This is necessary because Buckets_Access has an empty
   --  storage pool.

   -----------
   -- Clear --
   -----------

   procedure Clear (HT : in out Hash_Table_Type) is
   begin
      if HT.Busy > 0 then
         raise Program_Error with
           "attempt to tamper with elements (container is busy)";
      end if;

      pragma Assert (HT.Lock = 0);
      HT.Length := 0;
   end Clear;

   ---------------------
   -- Default_Modulus --
   ---------------------

   function Default_Modulus (Capacity : Count_Type) return Hash_Type is
   begin
      return Prime_Numbers.To_Prime (Capacity);
   end Default_Modulus;

   ---------------------------
   -- Delete_Node_Sans_Free --
   ---------------------------

   procedure Delete_Node_Sans_Free
     (HT : in out Hash_Table_Type;
      X  : Node_Access)
   is
      pragma Assert (X /= 0);

      Indx : Hash_Type;
      Prev : Node_Access;
      Curr : Node_Access;

   begin
      if HT.Length = 0 then
         raise Program_Error with
           "attempt to delete node from empty hashed container";
      end if;

      Indx := Index (HT, X);
      Prev := HT.Buckets (Indx);

      if Prev = 0 then
         raise Program_Error with
           "attempt to delete node from empty hash bucket";
      end if;

      if Prev = X then
         HT.Buckets (Indx) := Get_Next (HT, Prev);
         HT.Length := HT.Length - 1;
         return;
      end if;

      if HT.Length = 1 then
         raise Program_Error with
           "attempt to delete node not in its proper hash bucket";
      end if;

      loop
         Curr := Get_Next (HT, Prev);

         if Curr = 0 then
            raise Program_Error with
              "attempt to delete node not in its proper hash bucket";
         end if;

         if Curr = X then
            Set_Next (HT, Node => Prev, Next => Get_Next (HT, Curr));
            HT.Length := HT.Length - 1;
            return;
         end if;

         Prev := Curr;
      end loop;
   end Delete_Node_Sans_Free;

   -----------
   -- First --
   -----------

   function First (HT : Hash_Table_Type) return Node_Access is
      Indx : Hash_Type;

   begin
      if HT.Length = 0 then
         return 0;
      end if;

      Indx := HT.Buckets'First;
      loop
         if HT.Buckets (Indx) /= 0 then
            return HT.Buckets (Indx);
         end if;

         Indx := Indx + 1;
      end loop;
   end First;

   ----------
   -- Free --
   ----------

   procedure Free (HT : in out Hash_Table_Type; X : in out Count_Type) is
      N : Nodes_Type renames HT.Nodes;

   begin
      if X = 0 then
         return;
      end if;

      pragma Assert (X in N'Range);

      --  explanation of semantics of HT.Free is required here???

      if HT.Length = 0 then
         Set_Next (HT, Node => X, Next => X);
         Set_Has_Element (HT, Node => X, Has_Element => false);
         X := 0;
         return;
      end if;

      pragma Assert (HT.Free <= N'Last);

      Set_Has_Element (HT, Node => X, Has_Element => false);
      Set_Next (HT, Node => X, Next => HT.Free);
      HT.Free := X;
      X := 0;
   end Free;

   ---------------------------
   -- Generic_Allocate_Node --
   ---------------------------

   procedure Generic_Allocate_Node
     (HT : in out Hash_Table_Type;
      X  : out Count_Type)
   is
      N : Nodes_Type renames HT.Nodes;

   begin
      if HT.Length >= HT.Capacity then
         raise Storage_Error with "not enough capacity";
      end if;

      if HT.Length = 0
        or else HT.Free = 0
      then
         X := HT.Length + 1;
         Initialize_Node (N (X));
         HT.Free := 0;  -- we're allocating from initialized storage

      else
         pragma Assert (HT.Free in N'Range);

         X := HT.Free;
         Initialize_Node (N (X));
         HT.Free := Get_Next (HT, X);
      end if;

      Set_Next (HT, Node => X, Next => 0);
   end Generic_Allocate_Node;

   -------------------
   -- Generic_Equal --
   -------------------

   function Generic_Equal
     (L, R : Hash_Table_Type) return Boolean
   is
      L_Index : Hash_Type;
      L_Node  : Node_Access;

      N : Count_Type;

   begin
      if L'Address = R'Address then
         return True;
      end if;

      if L.Length /= R.Length then
         return False;
      end if;

      if L.Length = 0 then
         return True;
      end if;

      --  Find the first node of hash table L

      L_Index := L.Buckets'First;
      loop
         L_Node := L.Buckets (L_Index);
         exit when L_Node /= 0;
         L_Index := L_Index + 1;
      end loop;

      --  For each node of hash table L, search for an equivalent node in hash
      --  table R.

      N := L.Length;
      loop
         if not Find (HT => R, Key => L_Node) then
            return False;
         end if;

         N := N - 1;

         L_Node := Get_Next (L, L_Node);

         if L_Node = 0 then
            --  We have exhausted the nodes in this bucket

            if N = 0 then
               return True;
            end if;

            --  Find the next bucket

            loop
               L_Index := L_Index + 1;
               L_Node := L.Buckets (L_Index);
               exit when L_Node /= 0;
            end loop;
         end if;
      end loop;
   end Generic_Equal;

   -----------------------
   -- Generic_Iteration --
   -----------------------

   procedure Generic_Iteration (HT : Hash_Table_Type) is
      Node : Node_Access;

   begin
      if HT.Length = 0 then
         return;
      end if;

      for Indx in HT.Buckets'Range loop
         Node := HT.Buckets (Indx);
         while Node /= 0 loop
            Process (Node);
            Node := Get_Next (HT, Node);
         end loop;
      end loop;
   end Generic_Iteration;

   ------------------
   -- Generic_Read --
   ------------------

   procedure Generic_Read
     (Stream : not null access Root_Stream_Type'Class;
      HT     : out Hash_Table_Type)
   is
      N    : Count_Type'Base;
      Node : Node_Access;

   begin
      Clear (HT);  -- clear now, or later after checks? ???

      Count_Type'Base'Read (Stream, N);

      if N < 0 then
         raise Program_Error with "stream appears to be corrupt";
      end if;

      if N = 0 then
         return;
      end if;

      if N > HT.Capacity then
         raise Storage_Error with "not enough capacity";  -- ???
      end if;

      for J in 1 .. N loop
         Allocate_Node (HT, Node);

         declare
            Indx : constant Hash_Type := Index (HT, Node);
            B    : Node_Access renames HT.Buckets (Indx);
         begin
            Set_Next (HT, Node => Node, Next => B);
            B := Node;
         end;

         HT.Length := HT.Length + 1;
      end loop;
   end Generic_Read;

   -------------------
   -- Generic_Write --
   -------------------

   procedure Generic_Write
     (Stream : not null access Root_Stream_Type'Class;
      HT     : Hash_Table_Type)
   is
      procedure Write (Node : Node_Access);
      pragma Inline (Write);

      procedure Write is new Generic_Iteration (Write);

      -----------
      -- Write --
      -----------

      procedure Write (Node : Node_Access) is
      begin
         Write (Stream, Node);
      end Write;

   begin
      --  See Generic_Read for an explanation of why we do not stream out the
      --  buckets array length too.

      Count_Type'Base'Write (Stream, HT.Length);
      Write (HT);
   end Generic_Write;

   -----------
   -- Index --
   -----------

   function Index
     (HT   : Hash_Table_Type;
      Node : Node_Access) return Hash_Type
   is
      H : constant Hash_Type := Hash_Node (HT, Node);
      I : constant Hash_Type := H mod HT.Buckets'Length;  -- TODO ???

   begin
      return HT.Buckets'First + I;
   end Index;

   ----------
   -- Next --
   ----------

   function Next
     (HT   : Hash_Table_Type;
      Node : Node_Access) return Node_Access
   is
      Result : Node_Access := Get_Next (HT, Node);

   begin
      if Result /= 0 then
         return Result;
      end if;

      for Indx in Index (HT, Node) + 1 .. HT.Buckets'Last loop
         Result := HT.Buckets (Indx);

         if Result /= 0 then
            return Result;
         end if;
      end loop;

      return 0;
   end Next;

   ----------------------
   -- Reserve_Capacity --
   ----------------------

   procedure Reserve_Capacity
     (HT : Hash_Table_Type;
      N  : Count_Type)
   is
   begin
      if N > HT.Nodes'Length then
         raise Storage_Error; -- what exception here???
      end if;

      --  check busy bits???
   end Reserve_Capacity;

   ---------
   -- Vet --
   ---------

   function Vet (HT : Hash_Table_Type; Node : Node_Access) return Boolean is
      X, Y : Node_Access;

   begin
--        if Position.Node = 0 then
--           return Position.Container = null;
--        end if;

--        if Position.Container = null then
--           return False;
--        end if;

      if HT.Capacity = 0
        or else HT.Length = 0
      then
         return False;
      end if;

      if Node not in HT.Nodes'Range then
         return False;
      end if;

      if Node = Get_Next (HT, Node) then
         return False;
      end if;

      X := HT.Buckets (Index (HT, Node));

      for J in 1 .. HT.Length loop
         if X = Node then
            return True;
         end if;

         if X = 0 then
            return False;
         end if;

         if X not in HT.Nodes'Range then
            return False;
         end if;

         Y := Get_Next (HT, X);

         if X = Y then  --  to prevent unnecessary looping
            return False;
         end if;

         X := Y;
      end loop;

      return False;
   end Vet;

end Verified_Hash_Tables.Generic_Operations;
