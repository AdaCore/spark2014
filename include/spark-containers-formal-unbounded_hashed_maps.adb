------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--               SPARK.CONTAINERS.FORMAL.UNBOUNDED_HASHED_MAPS              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--          Copyright (C) 2022-2022, Free Software Foundation, Inc.         --
--                                                                          --
-- SPARK is free software;  you can  redistribute it and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion. SPARK is distributed in the hope that it will be useful, but WITH- --
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
--                                                                          --
------------------------------------------------------------------------------

with Ada.Containers.Hash_Tables.Generic_Formal_Operations;
pragma Elaborate_All (Ada.Containers.Hash_Tables.Generic_Formal_Operations);

with Ada.Containers.Hash_Tables.Generic_Formal_Keys;
pragma Elaborate_All (Ada.Containers.Hash_Tables.Generic_Formal_Keys);

with Ada.Containers.Prime_Numbers; use Ada.Containers.Prime_Numbers;

with SPARK.Big_Integers;
use SPARK.Big_Integers;

with Ada.Unchecked_Deallocation;

with System; use type System.Address;

package body SPARK.Containers.Formal.Unbounded_Hashed_Maps with
  SPARK_Mode => Off
is
   -----------------------
   -- Local Subprograms --
   -----------------------

   function Equivalent_Keys
     (Key  : Key_Type;
      Node : Node_Type) return Boolean;
   --  Test if the key of Node is equivalent to Key using the function provided
   --  as a generic parameter.

   pragma Inline (Equivalent_Keys);

   procedure Free
     (HT : in out Map;
      X  : Count_Type);
   --  Cleanly remove a node from the Map and put it back in the free list

   generic
      with procedure Set_Element (Node : in out Node_Type);
   procedure Generic_Allocate
     (HT   : in out HT_Types.Hash_Table_Type;
      Node : out Count_Type);
   --  Allocate a new node i.e get it out of the free list

   function Hash_Node (Node : Node_Type) return Hash_Type;
   --  Hash the Node's Key using the Hash function provided as a generic
   --  parameter.

   pragma Inline (Hash_Node);

   function Next (Node : Node_Type) return Count_Type;
   --  Return the node following Node in the same Bucket. Useb by Hash_Tables
   --  operation's functions.

   pragma Inline (Next);

   procedure Set_Next (Node : in out Node_Type; Next : Count_Type);
   --  Set the node following Node. Useb by Hash_Tables operation's functions.
   pragma Inline (Set_Next);

   function Vet (Container : Map; Position : Cursor) return Boolean
   --  Check if Position is correct in Container

     with Inline;

   --  Convert Count_Type to Big_Interger

   package Conversions is new Signed_Conversions (Int => Count_Type);

   function Big (J : Count_Type) return Big_Integer renames
     Conversions.To_Big_Integer;
   --  Convert Count_Type to a Big_Integer

   procedure Resize (Container : in out Map; Size : Count_Type := 0) with
   --  Allocate a new larger Map

     Global => null,
     Post   => Model (Container) = Model (Container)'Old
                 and Length (Container) = Length (Container)'Old
                 and K_Keys_Included (Keys (Container), Keys (Container)'Old);

   --------------------------
   -- Local Instantiations --
   --------------------------

   procedure Finalize_Content is new Ada.Unchecked_Deallocation
     (Object => HT_Types.Hash_Table_Type,
      Name   => HT_Access);
   --  Deallocate a HT_Types.Hash_Table_Type

   package HT_Ops is
     new Hash_Tables.Generic_Formal_Operations
       (HT_Types  => HT_Types,
        Hash_Node => Hash_Node,
        Next      => Next,
        Set_Next  => Set_Next);

   package Key_Ops is
     new Hash_Tables.Generic_Formal_Keys
       (HT_Types        => HT_Types,
        Next            => Next,
        Set_Next        => Set_Next,
        Key_Type        => Key_Type,
        Hash            => Hash,
        Equivalent_Keys => Equivalent_Keys);

   ---------
   -- "=" --
   ---------

   function "=" (Left, Right : Map) return Boolean is
   begin
      if Length (Left) /= Length (Right) then
         return False;
      end if;

      if Length (Left) = 0 then
         return True;
      end if;

      declare
         Node  : Count_Type;
         ENode : Count_Type;

      begin
         Node := First (Left).Node;
         while Node /= 0 loop
            ENode :=
              Find
                (Container => Right,
                 Key       =>
                   KHT.Element (Left.Content.Nodes (Node).K_Holder)).Node;

            if ENode = 0 or else
              EHT.Element (Right.Content.Nodes (ENode).E_Holder) /=
              EHT.Element (Left.Content.Nodes (Node).E_Holder)
            then
               return False;
            end if;

            Node := HT_Ops.Next (Left.Content.all, Node);
         end loop;

         return True;
      end;
   end "=";

   ------------
   -- Adjust --
   ------------

   procedure Adjust (Container : in out Map) is
   begin
      if Container.Content = Empty_HT'Access then
         return;
      end if;

      declare
         New_Map : constant HT_Access :=
           new HT_Types.Hash_Table_Type
             (Container.Content.Capacity, Container.Content.Modulus);

      begin
         New_Map.Length := Container.Content.Length;
         New_Map.Free   := Container.Content.Free;

         --  Copy the nodes. The call to Adjust will make a proper copy of
         --  the holders.

         New_Map.Nodes (1 .. Container.Content.Capacity) :=
           Container.Content.Nodes (1 .. Container.Content.Capacity);

         --  There is no nodes to be added to the free list since Container and
         --  New_Map have the same size.

         --  Copy the buckets

         New_Map.Buckets (1 .. New_Map.Modulus) :=
           Container.Content.Buckets (1 .. New_Map.Modulus);

         --  Put the New_Map in the current container

         Container.Content := New_Map;
      end;
   end Adjust;

   ------------
   -- Assign --
   ------------

   procedure Assign (Target : in out Map; Source : Map) is
      procedure Insert_Element (Source_Node : Count_Type);
      pragma Inline (Insert_Element);

      procedure Insert_Elements is
        new HT_Ops.Generic_Iteration (Insert_Element);

      --------------------
      -- Insert_Element --
      --------------------

      procedure Insert_Element (Source_Node : Count_Type) is
         N : Node_Type renames Source.Content.Nodes (Source_Node);
      begin
         Insert (Target, KHT.Element (N.K_Holder), EHT.Element (N.E_Holder));
      end Insert_Element;

   --  Start of processing for Assign

   begin
      HT_Ops.Clear (Target.Content.all);
      Insert_Elements (Source.Content.all);
   end Assign;

   -----------
   -- Clear --
   -----------

   procedure Clear (Container : in out Map) is
   begin
      HT_Ops.Clear (Container.Content.all);
   end Clear;

   ------------------------
   -- Constant_Reference --
   ------------------------

   function Constant_Reference
     (Container : Map;
      Position  : Cursor) return not null access constant Element_Type
   is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with "Position cursor has no element";
      end if;

      pragma Assert
        (Vet (Container, Position),
         "bad cursor in function Constant_Reference");

      return
        EHT.Element_Access (Container.Content.Nodes (Position.Node).E_Holder);
   end Constant_Reference;

   function Constant_Reference
     (Container : Map;
      Key       : Key_Type) return not null access constant Element_Type
   is
      Node : constant Count_Type := Find (Container, Key).Node;

   begin
      if Node = 0 then
         raise Constraint_Error with
           "no element available because key not in map";
      end if;

      return EHT.Element_Access (Container.Content.Nodes (Node).E_Holder);
   end Constant_Reference;

   --------------
   -- Contains --
   --------------

   function Contains (Container : Map; Key : Key_Type) return Boolean is
   begin
      return Find (Container, Key) /= No_Element;
   end Contains;

   ----------
   -- Copy --
   ----------

   function Copy (Source : Map) return Map
   is
      Target : Map (Source.Modulus);

   begin
      if Source.Content = Empty_HT'Access then
         return Target;
      end if;

      --  The implicit call to Adjust will properly copy the element

      Target.Content := new HT_Types.Hash_Table_Type'(Source.Content.all);

      return Target;
   end Copy;

   ---------------------
   -- Default_Modulus --
   ---------------------

   function Default_Modulus (Capacity : Count_Type) return Hash_Type is
   begin
      return To_Prime (Capacity);
   end Default_Modulus;

   ------------
   -- Delete --
   ------------

   procedure Delete (Container : in out Map; Key : Key_Type) is
      X : Count_Type;

   begin
      Key_Ops.Delete_Key_Sans_Free (Container.Content.all, Key, X);

      if X = 0 then
         raise Constraint_Error with "attempt to delete key not in map";
      end if;

      Free (Container, X);
   end Delete;

   procedure Delete (Container : in out Map; Position : in out Cursor) is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with
           "Position cursor of Delete has no element";
      end if;

      pragma Assert (Vet (Container, Position), "bad cursor in Delete");

      HT_Ops.Delete_Node_Sans_Free (Container.Content.all, Position.Node);

      Free (Container, Position.Node);
      Position := No_Element;
   end Delete;

   -------------
   -- Element --
   -------------

   function Element (Container : Map; Key : Key_Type) return Element_Type is
      Node : constant Count_Type := Find (Container, Key).Node;

   begin
      if Node = 0 then
         raise Constraint_Error with
           "no element available because key not in map";
      end if;

      return EHT.Element (Container.Content.Nodes (Node).E_Holder);
   end Element;

   function Element (Container : Map; Position : Cursor) return Element_Type is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with "Position cursor equals No_Element";
      end if;

      pragma Assert
        (Vet (Container, Position), "bad cursor in function Element");

      return EHT.Element (Container.Content.Nodes (Position.Node).E_Holder);
   end Element;

   ---------------
   -- Empty_Map --
   ---------------

   function Empty_Map (Modulus : Hash_Type := 0) return Map is
      ((Ada.Finalization.Controlled with Modulus => Modulus,
                                         Content => Empty_HT'Access));

   ---------------------
   -- Equivalent_Keys --
   ---------------------

   function Equivalent_Keys
     (Key  : Key_Type;
      Node : Node_Type) return Boolean
   is
   begin
      return Equivalent_Keys (Key, KHT.Element (Node.K_Holder));
   end Equivalent_Keys;

   -------------
   -- Exclude --
   -------------

   procedure Exclude (Container : in out Map; Key : Key_Type) is
      X : Count_Type;
   begin
      Key_Ops.Delete_Key_Sans_Free (Container.Content.all, Key, X);
      Free (Container, X);
   end Exclude;

   --------------
   -- Finalize --
   --------------

   procedure Finalize (Container : in out Map) is
   begin
      if Container.Content /= Empty_HT'Access then
         declare
            HT : HT_Access := Container.Content;
         begin
            Container.Content := Empty_HT'Access;
            Finalize_Content (HT);
         end;
      end if;
   end Finalize;

   ----------
   -- Find --
   ----------

   function Find (Container : Map; Key : Key_Type) return Cursor is
      Node : constant Count_Type := Key_Ops.Find (Container.Content.all, Key);

   begin
      if Node = 0 then
         return No_Element;
      end if;

      return (Node => Node);
   end Find;

   -----------
   -- First --
   -----------

   function First (Container : Map) return Cursor is
      Node : constant Count_Type := HT_Ops.First (Container.Content.all);

   begin
      if Node = 0 then
         return No_Element;
      end if;

      return (Node => Node);
   end First;

   ------------------
   -- Formal_Model --
   ------------------

   package body Formal_Model is

      ----------
      -- Find --
      ----------

      function Find
        (Container : K.Sequence;
         Key       : Key_Type) return Count_Type
      is
      begin
         for I in 1 .. K.Length (Container) loop
            if Equivalent_Keys (Key, K.Get (Container, I)) then
               return I;
            end if;
         end loop;
         return 0;
      end Find;

      ---------------------
      -- K_Keys_Included --
      ---------------------

      function K_Keys_Included
        (Left  : K.Sequence;
         Right : K.Sequence) return Boolean
      is
      begin
         for I in 1 .. K.Length (Left) loop
            if not K.Contains (Right, 1, K.Length (Right), K.Get (Left, I))
            then
               return False;
            end if;
         end loop;

         return True;
      end K_Keys_Included;

      ----------
      -- Keys --
      ----------

      function Keys (Container : Map) return K.Sequence is
         Position : Count_Type := HT_Ops.First (Container.Content.all);
         R        : K.Sequence;

      begin
         --  Can't use First, Next or Element here, since they depend on models
         --  for their postconditions.

         while Position /= 0 loop
            R :=
              K.Add
                (R, KHT.Element (Container.Content.Nodes (Position).K_Holder));
            Position := HT_Ops.Next (Container.Content.all, Position);
         end loop;

         return R;
      end Keys;

      ----------------------------
      -- Lift_Abstraction_Level --
      ----------------------------

      procedure Lift_Abstraction_Level (Container : Map) is null;

      -----------------------
      -- Mapping_Preserved --
      -----------------------

      function Mapping_Preserved
        (K_Left  : K.Sequence;
         K_Right : K.Sequence;
         P_Left  : P.Map;
         P_Right : P.Map) return Boolean
      is
      begin
         for C of P_Left loop
            if not P.Has_Key (P_Right, C)
              or else P.Get (P_Left,  C) > K.Length (K_Left)
              or else P.Get (P_Right, C) > K.Length (K_Right)
              or else K.Get (K_Left,  P.Get (P_Left,  C)) /=
                      K.Get (K_Right, P.Get (P_Right, C))
            then
               return False;
            end if;
         end loop;

         return True;
      end Mapping_Preserved;

      -----------
      -- Model --
      -----------

      function Model (Container : Map) return M.Map is
         Position : Count_Type := HT_Ops.First (Container.Content.all);
         R        : M.Map;

      begin
         --  Can't use First, Next or Element here, since they depend on models
         --  for their postconditions.

         while Position /= 0 loop
            R :=
              M.Add
                (Container => R,
                 New_Key   =>
                   KHT.Element (Container.Content.Nodes (Position).K_Holder),
                 New_Item  =>
                   EHT.Element (Container.Content.Nodes (Position).E_Holder));

            Position := HT_Ops.Next (Container.Content.all, Position);
         end loop;

         return R;
      end Model;

      ---------------
      -- Positions --
      ---------------

      function Positions (Container : Map) return P.Map is
         I        : Count_Type := 1;
         Position : Count_Type := HT_Ops.First (Container.Content.all);
         R        : P.Map;

      begin
         --  Can't use First, Next or Element here, since they depend on models
         --  for their postconditions.

         while Position /= 0 loop
            R := P.Add (R, (Node => Position), I);
            pragma Assert (P.Length (R) = Big (I));
            Position := HT_Ops.Next (Container.Content.all, Position);
            I := I + 1;
         end loop;

         return R;
      end Positions;

   end Formal_Model;

   ----------
   -- Free --
   ----------

   procedure Free (HT : in out Map; X : Count_Type) is
   begin
      if X /= 0 then
         pragma Assert (X <= HT.Content.Capacity);
         HT.Content.Nodes (X).Has_Element := False;
         HT_Ops.Free (HT.Content.all, X);
      end if;
   end Free;

   ----------------------
   -- Generic_Allocate --
   ----------------------

   procedure Generic_Allocate
     (HT   : in out HT_Types.Hash_Table_Type;
      Node : out Count_Type)
   is
      procedure Allocate is
        new HT_Ops.Generic_Allocate (Set_Element);

   begin
      Allocate (HT, Node);
      HT.Nodes (Node).Has_Element := True;
   end Generic_Allocate;

   -----------------
   -- Has_Element --
   -----------------

   function Has_Element (Container : Map; Position : Cursor) return Boolean is
   begin
      if Position.Node < 1
           or else Position.Node > Container.Content.Nodes'Length
           or else not Container.Content.Nodes (Position.Node).Has_Element
      then
         return False;
      else
         return True;
      end if;
   end Has_Element;

   ---------------
   -- Hash_Node --
   ---------------

   function Hash_Node (Node : Node_Type) return Hash_Type is
   begin
      return Hash (KHT.Element (Node.K_Holder));
   end Hash_Node;

   -------------
   -- Include --
   -------------

   procedure Include
     (Container : in out Map;
      Key       : Key_Type;
      New_Item  : Element_Type)
   is
      Position : Cursor;
      Inserted : Boolean;

   begin
      Insert (Container, Key, New_Item, Position, Inserted);

      if not Inserted then
         declare
            P : constant Count_Type := Position.Node;
            N : Node_Type renames Container.Content.Nodes (P);
         begin
            KHT.Replace_Element (N.K_Holder, Key);
            EHT.Replace_Element (N.E_Holder, New_Item);
         end;
      end if;
   end Include;

   ------------
   -- Insert --
   ------------

   procedure Insert
     (Container : in out Map;
      Key       : Key_Type;
      New_Item  : Element_Type;
      Position  : out Cursor;
      Inserted  : out Boolean)
   is
      procedure Assign_Key (Node : in out Node_Type);
      pragma Inline (Assign_Key);

      procedure New_Node
        (HT   : in out HT_Types.Hash_Table_Type;
         Node : out Count_Type);
      pragma Inline (New_Node);

      procedure Local_Insert is
        new Key_Ops.Generic_Conditional_Insert (New_Node);

      procedure Allocate is
        new Generic_Allocate (Assign_Key);

      -----------------
      --  Assign_Key --
      -----------------

      procedure Assign_Key (Node : in out Node_Type) is
      begin
         KHT.Replace_Element (Node.K_Holder, Key);
         EHT.Replace_Element (Node.E_Holder, New_Item);
      end Assign_Key;

      --------------
      -- New_Node --
      --------------

      procedure New_Node
        (HT   : in out HT_Types.Hash_Table_Type;
         Node : out Count_Type)
      is
      begin
         Allocate (HT, Node);
      end New_Node;

   --  Start of processing for Insert

   begin
      if Container.Content.Nodes'Length = Length (Container)
      then
         Resize (Container);
      end if;

      Local_Insert (Container.Content.all, Key, Position.Node, Inserted);
   end Insert;

   procedure Insert
     (Container : in out Map;
      Key       : Key_Type;
      New_Item  : Element_Type)
   is
      Unused_Position : Cursor;
      Inserted        : Boolean;

   begin
      Insert (Container, Key, New_Item, Unused_Position, Inserted);

      if not Inserted then
         raise Constraint_Error with "attempt to insert key already in map";
      end if;
   end Insert;

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (Container : Map) return Boolean is
   begin
      return Length (Container) = 0;
   end Is_Empty;

   ---------
   -- Key --
   ---------

   function Key (Container : Map; Position : Cursor) return Key_Type is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with
           "Position cursor of function Key has no element";
      end if;

      pragma Assert (Vet (Container, Position), "bad cursor in function Key");

      return KHT.Element (Container.Content.Nodes (Position.Node).K_Holder);
   end Key;

   ------------
   -- Length --
   ------------

   function Length (Container : Map) return Count_Type is
   begin
      return Container.Content.Length;
   end Length;

   ----------
   -- Move --
   ----------

   procedure Move (Target : in out Map; Source : in out Map) is
   begin
      Finalize (Target);

      Target.Content := Source.Content;
      Source.Content := Empty_HT'Access;
   end Move;

   ----------
   -- Next --
   ----------

   function Next (Node : Node_Type) return Count_Type is
   begin
      return Node.Next;
   end Next;

   function Next (Container : Map; Position : Cursor) return Cursor is
   begin
      if Position.Node = 0 then
         return No_Element;
      end if;

      if not Has_Element (Container, Position) then
         raise Constraint_Error with "Position has no element";
      end if;

      pragma Assert (Vet (Container, Position), "bad cursor in function Next");

      declare
         Node : constant Count_Type :=
           HT_Ops.Next (Container.Content.all, Position.Node);

      begin
         if Node = 0 then
            return No_Element;
         end if;

         return (Node => Node);
      end;
   end Next;

   procedure Next (Container : Map; Position : in out Cursor) is
   begin
      Position := Next (Container, Position);
   end Next;

   ---------------
   -- Reference --
   ---------------

   function Reference
     (Container : not null access Map;
      Position  : Cursor) return not null access Element_Type
   is
   begin
      if not Has_Element (Container.all, Position) then
         raise Constraint_Error with "Position cursor has no element";
      end if;

      pragma Assert
        (Vet (Container.all, Position), "bad cursor in function Reference");

      return
        EHT.Element_Access (Container.Content.Nodes (Position.Node).E_Holder);
   end Reference;

   function Reference
     (Container : not null access Map;
      Key       : Key_Type) return not null access Element_Type
   is
      Node : constant Count_Type := Find (Container.all, Key).Node;

   begin
      if Node = 0 then
         raise Constraint_Error with
           "no element available because key not in map";
      end if;

      return EHT.Element_Access (Container.Content.Nodes (Node).E_Holder);
   end Reference;

   -------------
   -- Replace --
   -------------

   procedure Replace
     (Container : in out Map;
      Key       : Key_Type;
      New_Item  : Element_Type)
   is
      Node : constant Count_Type := Key_Ops.Find (Container.Content.all, Key);

   begin
      if Node = 0 then
         raise Constraint_Error with "attempt to replace key not in map";
      end if;

      declare
         N : Node_Type renames Container.Content.Nodes (Node);
      begin
         KHT.Replace_Element (N.K_Holder, Key);
         EHT.Replace_Element (N.E_Holder, New_Item);
      end;
   end Replace;

   ---------------------
   -- Replace_Element --
   ---------------------

   procedure Replace_Element
     (Container : in out Map;
      Position  : Cursor;
      New_Item  : Element_Type)
   is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with
           "Position cursor of Replace_Element has no element";
      end if;

      pragma Assert
        (Vet (Container, Position), "bad cursor in Replace_Element");

      EHT.Replace_Element
        (Container.Content.Nodes (Position.Node).E_Holder, New_Item);
   end Replace_Element;

   ------------
   -- Resize --
   ------------

   procedure Resize (Container : in out Map; Size : Count_Type := 0) is
      Min_Size : constant Count_Type := 100;
      New_Size : constant Count_Type := Count_Type'Max (Min_Size, Size);

      CC : HT_Access renames Container.Content;

   begin
      if CC = Empty_HT'Access then
         CC := new HT_Types.Hash_Table_Type (New_Size, Container.Modulus);
         return;
      end if;

      if CC.Nodes'Length = Count_Type'Last then
         raise Constraint_Error with "Map already at max size";
      end if;

      if Size /= 0 and then CC.Capacity >= Size then
         return;
      end if;

      declare
         Next_Size : constant Count_Type :=
           (if CC.Nodes'Length < Count_Type'Last / 2
            then 2 * CC.Nodes'Length
            else Count_Type'Last);
         New_Map : constant HT_Access :=
           new HT_Types.Hash_Table_Type (Count_Type'Max (New_Size, Next_Size),
                                         Container.Modulus);

      begin

         --  Make a perfect copy of Container.Content

         New_Map.Length := Container.Content.Length;
         New_Map.Free   := Container.Content.Free;

         for J in 1 .. Container.Content.Capacity loop
            declare
               New_Node : Node_Type renames New_Map.Nodes (J);
               Old_Node : Node_Type renames CC.Nodes (J);

            begin
               KHT.Move (New_Node.K_Holder, Old_Node.K_Holder);
               EHT.Move (New_Node.E_Holder, Old_Node.E_Holder);
               New_Node.Next             := Old_Node.Next;
               New_Node.Has_Element      := Old_Node.Has_Element;
            end;
         end loop;

         New_Map.Buckets (1 .. Container.Modulus) :=
           Container.Content.Buckets (1 .. Container.Modulus);

         --  Set up the Free list.
         --  It might be optimized by checking if New_Map.Free < 0 and,
         --  then just do nothing but it would make the unit relies on the
         --  current implementation of the hashed table. A change in the
         --  hashed table could thus create a sneaky bug here.

         for J in Container.Content.Length + 1 .. New_Map.Capacity loop
            New_Map.Nodes (J).Has_Element := False;
            HT_Ops.Free (New_Map.all, J);
         end loop;

         --  The table must be manually deallocated because it is not
         --  Controlled. Only Container (and the holder) are controlled
         --  here. This will not cause leaks since the ownership of the
         --  elements has been moved to New_Map.

         Finalize (Container);
         CC := New_Map;
      end;
   end Resize;

   --------------
   -- Set_Next --
   --------------

   procedure Set_Next (Node : in out Node_Type; Next : Count_Type) is
   begin
      Node.Next := Next;
   end Set_Next;

   ---------
   -- Vet --
   ---------

   function Vet (Container : Map; Position : Cursor) return Boolean is
   begin
      if Position.Node = 0 then
         return True;
      end if;

      declare
         X : Count_Type;

      begin
         if Container.Content = Empty_HT'Access then
            return False;
         end if;

         if Container.Content.Length = 0 then
            return False;
         end if;

         if Container.Content.Capacity = 0 then
            return False;
         end if;

         if Container.Content.Buckets'Length = 0 then
            return False;
         end if;

         if Position.Node > Container.Content.Capacity then
            return False;
         end if;

         if Container.Content.Nodes (Position.Node).Next = Position.Node then
            return False;
         end if;

         X :=
           Container.Content.Buckets
             (Key_Ops.Index
                (Container.Content.all,
                 KHT.Element
                   (Container.Content.Nodes (Position.Node).K_Holder)));

         for J in 1 .. Container.Content.Length loop
            if X = Position.Node then
               return True;
            end if;

            if X = 0 then
               return False;
            end if;

            if X = Container.Content.Nodes (X).Next then

               --  Prevent unnecessary looping

               return False;
            end if;

            X := Container.Content.Nodes (X).Next;
         end loop;

         return False;
      end;
   end Vet;

end SPARK.Containers.Formal.Unbounded_Hashed_Maps;
