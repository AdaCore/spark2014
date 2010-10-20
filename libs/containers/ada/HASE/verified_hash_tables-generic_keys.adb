------------------------------------------------------------------------------
--                                                                          --
--                         GNAT LIBRARY COMPONENTS                          --
--                                                                          --
--                      A D A . C O N T A I N E R S .                       --
--             H A S H _ T A B L E S . G E N E R I C _ K E Y S              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--          Copyright (C) 2004-2010, Free Software Foundation, Inc.         --
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

package body Verified_Hash_Tables.Generic_Keys is

   --------------------------
   -- Delete_Key_Sans_Free --
   --------------------------

   procedure Delete_Key_Sans_Free
     (HT  : in out Hash_Table_Type;
      Key : Key_Type;
      X   : out Node_Access)
   is
      Indx : Hash_Type;
      Prev : Node_Access;

   begin
      if HT.Length = 0 then
         X := 0;
         return;
      end if;

      Indx := Index (HT, Key);
      X := HT.Buckets (Indx);

      if X = 0 then
         return;
      end if;

      if Equivalent_Keys (Key, HT, X) then
         if HT.Busy > 0 then
            raise Program_Error with
              "attempt to tamper with elements (container is busy)";
         end if;
         HT.Buckets (Indx) := Get_Next (HT, X);
         HT.Length := HT.Length - 1;
         return;
      end if;

      loop
         Prev := X;
         X := Get_Next (HT, Prev);

         if X = 0 then
            return;
         end if;

         if Equivalent_Keys (Key, HT, X) then
            if HT.Busy > 0 then
               raise Program_Error with
                 "attempt to tamper with elements (container is busy)";
            end if;
            Set_Next (HT, Node => Prev, Next => Get_Next (HT, X));
            HT.Length := HT.Length - 1;
            return;
         end if;
      end loop;
   end Delete_Key_Sans_Free;

   ----------
   -- Find --
   ----------

   function Find
     (HT  : Hash_Table_Type;
      Key : Key_Type) return Node_Access is

      Indx : Hash_Type;
      Node : Node_Access;

   begin
      if HT.Length = 0 then
         return 0;
      end if;

      Indx := Index (HT, Key);
      Node := HT.Buckets (Indx);
      while Node /= 0 loop
         if Equivalent_Keys (Key, HT, Node) then
            return Node;
         end if;
         Node := Get_Next (HT, Node);
      end loop;

      return 0;
   end Find;

   --------------------------------
   -- Generic_Conditional_Insert --
   --------------------------------

   procedure Generic_Conditional_Insert
     (HT       : in out Hash_Table_Type;
      Key      : Key_Type;
      Node     : out Node_Access;
      Inserted : out Boolean)
   is
      Indx : constant Hash_Type := Index (HT, Key);
      B    : Node_Access renames HT.Buckets (Indx);

   begin
      if B = 0 then
         if HT.Busy > 0 then
            raise Program_Error with
              "attempt to tamper with elements (container is busy)";
         end if;

         if HT.Length = Count_Type'Last then
            raise Constraint_Error;
         end if;

         Node := New_Node (Next => 0);
         Inserted := True;

         B := Node;
         HT.Length := HT.Length + 1;

         return;
      end if;

      Node := B;
      loop
         if Equivalent_Keys (Key, HT, Node) then
            Inserted := False;
            return;
         end if;

         Node := Get_Next (HT, Node);

         exit when Node = 0;
      end loop;

      if HT.Busy > 0 then
         raise Program_Error with
           "attempt to tamper with elements (container is busy)";
      end if;

      if HT.Length = Count_Type'Last then
         raise Constraint_Error;
      end if;

      Node := New_Node (Next => B);
      Inserted := True;

      B := Node;
      HT.Length := HT.Length + 1;
   end Generic_Conditional_Insert;

   -----------
   -- Index --
   -----------

   function Index
     (HT  : Hash_Table_Type;
      Key : Key_Type) return Hash_Type
   is
      H : constant Hash_Type := Hash (Key);
      I : constant Hash_Type := H mod HT.Buckets'Length;  -- TODO! ???

   begin
      return HT.Buckets'First + I;
   end Index;

   -----------------------------
   -- Generic_Replace_Element --
   -----------------------------

   procedure Generic_Replace_Element
     (HT   : in out Hash_Table_Type;
      Node : Node_Access;
      Key  : Key_Type)
   is
      pragma Assert (HT.Length > 0);
      pragma Assert (Node /= 0);

      Old_Hash : constant Hash_Type := Hash (Node);

      Old_Indx : constant Hash_Type :=
                   HT.Buckets'First + Old_Hash mod HT.Buckets'Length;

      New_Hash : constant Hash_Type := Hash (Key);

      New_Indx : constant Hash_Type :=
                   HT.Buckets'First + New_Hash mod HT.Buckets'Length;

      New_Bucket : Count_Type renames HT.Buckets (New_Indx);
      N, M       : Node_Access;

   begin
      if Equivalent_Keys (Key, HT, Node) then
         pragma Assert (New_Hash = Old_Hash);

         if HT.Lock > 0 then
            raise Program_Error with
              "attempt to tamper with cursors (container is locked)";
         end if;

         --  We can change a node's key to Key (that's what Assign is for), but
         --  only if Key is not already in the hash table. (In a unique-key
         --  hash table as this one a key is mapped to exactly one node only.)
         --  The exception is when Key is mapped to Node, in which case the
         --  change is allowed.

         Assign (Node, Key);
         pragma Assert (Hash (Node) = New_Hash);
         pragma Assert (Equivalent_Keys (Key, HT, Node));
         return;
      end if;

      --  Key is not equivalent to Node, so we now have to determine if it's
      --  equivalent to some other node in the hash table. This is the case
      --  irrespective of whether Key is in the same or a different bucket from
      --  Node.

      N := New_Bucket;
      while N /= 0 loop
         if Equivalent_Keys (Key, HT, N) then
            pragma Assert (N /= Node);
            raise Program_Error with
              "attempt to replace existing element";
         end if;

         N := Get_Next (HT, N);
      end loop;

      --  We have determined that Key is not already in the hash table, so
      --  the change is tenatively allowed. We now perform the standard
      --  checks to determine whether the hash table is locked (because you
      --  cannot change an element while it's in use by Query_Element or
      --  Update_Element), or if the container is busy (because moving a
      --  node to a different bucket would interfere with iteration).

      if Old_Indx = New_Indx then
         --  The node is already in the bucket implied by Key. In this case
         --  we merely change its value without moving it.

         if HT.Lock > 0 then
            raise Program_Error with
              "attempt to tamper with cursors (container is locked)";
         end if;

         Assign (Node, Key);
         pragma Assert (Hash (Node) = New_Hash);
         pragma Assert (Equivalent_Keys (Key, HT, Node));
         return;
      end if;

      --  The node is a bucket different from the bucket implied by Key

      if HT.Busy > 0 then
         raise Program_Error with
           "attempt to tamper with elements (container is busy)";
      end if;

      --  Do the assignment first, before moving the node, so that if Assign
      --  propagates an exception, then the hash table will not have been
      --  modified (except for any possible side-effect Assign had on Node).

      Assign (Node, Key);
      pragma Assert (Hash (Node) = New_Hash);
      pragma Assert (Equivalent_Keys (Key, HT, Node));

      --  Now we can safely remove the node from its current bucket

      N := HT.Buckets (Old_Indx);
      pragma Assert (N /= 0);

      if N = Node then
         HT.Buckets (Old_Indx) := Get_Next (HT, Node);

      else
         pragma Assert (HT.Length > 1);

         loop
            M := Get_Next (HT, N);
            pragma Assert (M /= 0);

            if M = Node then
               Set_Next (HT, Node => N, Next => Get_Next (HT, Node));
               exit;
            end if;

            N := M;
         end loop;
      end if;

      --  Now we link the node into its new bucket (corresponding to Key)

      Set_Next (HT, Node => Node, Next => New_Bucket);
      New_Bucket := Node;
   end Generic_Replace_Element;

end Verified_Hash_Tables.Generic_Keys;
