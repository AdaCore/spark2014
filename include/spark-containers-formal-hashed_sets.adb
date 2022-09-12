------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--                   SPARK.CONTAINERS.FORMAL.HASHED_SETS                    --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--          Copyright (C) 2004-2022, Free Software Foundation, Inc.         --
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

with Ada.Containers.Hash_Tables.Generic_Formal_Keys;

with Ada.Containers.Prime_Numbers; use Ada.Containers.Prime_Numbers;

with System; use type System.Address;

package body SPARK.Containers.Formal.Hashed_Sets with
  SPARK_Mode => Off
is
   -----------------------
   -- Local Subprograms --
   -----------------------

   --  All need comments ???

   procedure Difference (Left : Set; Right : Set; Target : in out Set);

   function Equivalent_Keys
     (Key  : Element_Type;
      Node : Node_Type) return Boolean;
   pragma Inline (Equivalent_Keys);

   procedure Free
     (HT : in out Set;
      X  : Count_Type);

   generic
      with procedure Set_Element (Node : in out Node_Type);
   procedure Generic_Allocate
     (HT   : in out Hash_Table_Type;
      Node : out Count_Type);

   function Hash_Node (Node : Node_Type) return Hash_Type;
   pragma Inline (Hash_Node);

   procedure Insert
     (Container : in out Set;
      New_Item  : Element_Type;
      Node      : out Count_Type;
      Inserted  : out Boolean);

   procedure Intersection
     (Left   : Set;
      Right  : Set;
      Target : in out Set);

   function Is_In
     (HT  : Set;
      Key : Node_Type) return Boolean;
   pragma Inline (Is_In);

   procedure Set_Element (Node : in out Node_Type; Item : Element_Type);
   pragma Inline (Set_Element);

   function Next (Node : Node_Type) return Count_Type;
   pragma Inline (Next);

   procedure Set_Next (Node : in out Node_Type; Next : Count_Type);
   pragma Inline (Set_Next);

   function Vet (Container : Set; Position : Cursor) return Boolean
     with Inline;

   --------------------------
   -- Local Instantiations --
   --------------------------

   package HT_Ops is new Hash_Tables.Generic_Formal_Operations
     (HT_Types  => HT_Types,
      Hash_Node => Hash_Node,
      Next      => Next,
      Set_Next  => Set_Next);

   package Element_Keys is new Hash_Tables.Generic_Formal_Keys
     (HT_Types        => HT_Types,
      Next            => Next,
      Set_Next        => Set_Next,
      Key_Type        => Element_Type,
      Hash            => Hash,
      Equivalent_Keys => Equivalent_Keys);

   procedure Replace_Element is
     new Element_Keys.Generic_Replace_Element (Hash_Node, Set_Element);

   ---------
   -- "=" --
   ---------

   function "=" (Left, Right : Set) return Boolean is
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
         Node  := First (Left).Node;
         while Node /= 0 loop
            ENode :=
              Find
                (Container => Right,
                 Item      => Left.Content.Nodes (Node).Element).Node;

            if ENode = 0
              or else Right.Content.Nodes (ENode).Element /=
              Left.Content.Nodes (Node).Element
            then
               return False;
            end if;

            Node := HT_Ops.Next (Left.Content, Node);
         end loop;

         return True;
      end;
   end "=";

   ------------
   -- Assign --
   ------------

   procedure Assign (Target : in out Set; Source : Set) is
      procedure Insert_Element (Source_Node : Count_Type);

      procedure Insert_Elements is
        new HT_Ops.Generic_Iteration (Insert_Element);

      --------------------
      -- Insert_Element --
      --------------------

      procedure Insert_Element (Source_Node : Count_Type) is
         N        : Node_Type renames Source.Content.Nodes (Source_Node);
         Unused_X : Count_Type;
         B        : Boolean;

      begin
         Insert (Target, N.Element, Unused_X, B);
         pragma Assert (B);
      end Insert_Element;

   --  Start of processing for Assign

   begin
      if Target.Capacity < Length (Source) then
         raise Storage_Error with "not enough capacity";  -- SE or CE? ???
      end if;

      HT_Ops.Clear (Target.Content);
      Insert_Elements (Source.Content);
   end Assign;

   --------------
   -- Capacity --
   --------------

   function Capacity (Container : Set) return Count_Type is
   begin
      return Container.Content.Nodes'Length;
   end Capacity;

   -----------
   -- Clear --
   -----------

   procedure Clear (Container : in out Set) is
   begin
      HT_Ops.Clear (Container.Content);
   end Clear;

   ------------------------
   -- Constant_Reference --
   ------------------------

   function Constant_Reference
     (Container : aliased Set;
      Position  : Cursor) return not null access constant Element_Type
   is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with "Position cursor equals No_Element";
      end if;

      pragma Assert
        (Vet (Container, Position), "bad cursor in function Element");

      return Container.Content.Nodes (Position.Node).Element'Access;
   end Constant_Reference;

   --------------
   -- Contains --
   --------------

   function Contains (Container : Set; Item : Element_Type) return Boolean is
   begin
      return Find (Container, Item) /= No_Element;
   end Contains;

   ----------
   -- Copy --
   ----------

   function Copy
     (Source   : Set;
      Capacity : Count_Type := 0) return Set
   is
      C      : constant Count_Type :=
                 Count_Type'Max (Capacity, Source.Capacity);
      Cu     : Cursor;
      H      : Hash_Type;
      N      : Count_Type;
      Target : Set (C, Source.Modulus);

   begin
      if 0 < Capacity and then Capacity < Source.Capacity then
         raise Capacity_Error;
      end if;

      Target.Content.Length := Source.Content.Length;
      Target.Content.Free := Source.Content.Free;

      H := 1;
      while H <= Source.Modulus loop
         Target.Content.Buckets (H) := Source.Content.Buckets (H);
         H := H + 1;
      end loop;

      N := 1;
      while N <= Source.Capacity loop
         Target.Content.Nodes (N) := Source.Content.Nodes (N);
         N := N + 1;
      end loop;

      while N <= C loop
         Cu := (Node => N);
         Free (Target, Cu.Node);
         N := N + 1;
      end loop;

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

   procedure Delete (Container : in out Set; Item : Element_Type) is
      X : Count_Type;

   begin
      Element_Keys.Delete_Key_Sans_Free (Container.Content, Item, X);

      if X = 0 then
         raise Constraint_Error with "attempt to delete element not in set";
      end if;

      Free (Container, X);
   end Delete;

   procedure Delete (Container : in out Set; Position : in out Cursor) is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with "Position cursor has no element";
      end if;

      pragma Assert (Vet (Container, Position), "bad cursor in Delete");

      HT_Ops.Delete_Node_Sans_Free (Container.Content, Position.Node);
      Free (Container, Position.Node);

      Position := No_Element;
   end Delete;

   ----------------
   -- Difference --
   ----------------

   procedure Difference (Target : in out Set; Source : Set) is
      Src_Last   : Count_Type;
      Src_Length : Count_Type;
      Src_Node   : Count_Type;
      Tgt_Node   : Count_Type;

      TN : Nodes_Type renames Target.Content.Nodes;
      SN : Nodes_Type renames Source.Content.Nodes;

   begin
      Src_Length := Source.Content.Length;

      if Src_Length = 0 then
         return;
      end if;

      if Src_Length >= Target.Content.Length then
         Tgt_Node := HT_Ops.First (Target.Content);
         while Tgt_Node /= 0 loop
            if Element_Keys.Find (Source.Content, TN (Tgt_Node).Element) /= 0
            then
               declare
                  X : constant Count_Type := Tgt_Node;
               begin
                  Tgt_Node := HT_Ops.Next (Target.Content, Tgt_Node);
                  HT_Ops.Delete_Node_Sans_Free (Target.Content, X);
                  Free (Target, X);
               end;

            else
               Tgt_Node := HT_Ops.Next (Target.Content, Tgt_Node);
            end if;
         end loop;

         return;
      else
         Src_Node := HT_Ops.First (Source.Content);
         Src_Last := 0;
      end if;

      while Src_Node /= Src_Last loop
         Tgt_Node := Element_Keys.Find (Target.Content, SN (Src_Node).Element);

         if Tgt_Node /= 0 then
            HT_Ops.Delete_Node_Sans_Free (Target.Content, Tgt_Node);
            Free (Target, Tgt_Node);
         end if;

         Src_Node := HT_Ops.Next (Source.Content, Src_Node);
      end loop;
   end Difference;

   procedure Difference (Left : Set; Right : Set; Target : in out Set) is
      procedure Process (L_Node : Count_Type);

      procedure Iterate is
        new HT_Ops.Generic_Iteration (Process);

      -------------
      -- Process --
      -------------

      procedure Process (L_Node : Count_Type) is
         B        : Boolean;
         E        : Element_Type renames Left.Content.Nodes (L_Node).Element;
         Unused_X : Count_Type;

      begin
         if Find (Right, E).Node = 0 then
            Insert (Target, E, Unused_X, B);
            pragma Assert (B);
         end if;
      end Process;

   --  Start of processing for Difference

   begin
      Iterate (Left.Content);
   end Difference;

   function Difference (Left : Set; Right : Set) return Set is
   begin
      if Length (Left) = 0 then
         return Empty_Set;
      end if;

      if Length (Right) = 0 then
         return Copy (Left);
      end if;

      declare
         C : constant Count_Type := Length (Left);
         H : constant Hash_Type := Default_Modulus (C);
      begin
         return S : Set (C, H) do
            Difference (Left, Right, Target => S);
         end return;
      end;
   end Difference;

   -------------
   -- Element --
   -------------

   function Element
     (Container : Set;
      Position  : Cursor) return Element_Type
   is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with "Position cursor equals No_Element";
      end if;

      pragma Assert
        (Vet (Container, Position), "bad cursor in function Element");

      return Container.Content.Nodes (Position.Node).Element;
   end Element;

   ---------------------
   -- Equivalent_Keys --
   ---------------------

   function Equivalent_Keys
     (Key  : Element_Type;
      Node : Node_Type) return Boolean
   is
   begin
      return Equivalent_Elements (Key, Node.Element);
   end Equivalent_Keys;

   ---------------------
   -- Equivalent_Sets --
   ---------------------

   function Equivalent_Sets (Left, Right : Set) return Boolean is

      function Find_Equivalent_Key
        (R_HT   : Hash_Table_Type;
         L_Node : Node_Type) return Boolean;
      pragma Inline (Find_Equivalent_Key);

      function Is_Equivalent is
        new HT_Ops.Generic_Equal (Find_Equivalent_Key);

      -------------------------
      -- Find_Equivalent_Key --
      -------------------------

      function Find_Equivalent_Key
        (R_HT   : Hash_Table_Type;
         L_Node : Node_Type) return Boolean
      is
         R_Index : constant Hash_Type :=
                     Element_Keys.Index (R_HT, L_Node.Element);
         R_Node  : Count_Type := R_HT.Buckets (R_Index);
         RN      : Nodes_Type renames R_HT.Nodes;

      begin
         loop
            if R_Node = 0 then
               return False;
            end if;

            if Equivalent_Elements
                 (L_Node.Element, RN (R_Node).Element)
            then
               return True;
            end if;

            R_Node := HT_Ops.Next (R_HT, R_Node);
         end loop;
      end Find_Equivalent_Key;

   --  Start of processing for Equivalent_Sets

   begin
      return Is_Equivalent (Left.Content, Right.Content);
   end Equivalent_Sets;

   -------------
   -- Exclude --
   -------------

   procedure Exclude (Container : in out Set; Item : Element_Type) is
      X : Count_Type;
   begin
      Element_Keys.Delete_Key_Sans_Free (Container.Content, Item, X);
      Free (Container, X);
   end Exclude;

   ----------
   -- Find --
   ----------

   function Find
     (Container : Set;
      Item      : Element_Type) return Cursor
   is
      Node : constant Count_Type :=
        Element_Keys.Find (Container.Content, Item);

   begin
      if Node = 0 then
         return No_Element;
      end if;

      return (Node => Node);
   end Find;

   -----------
   -- First --
   -----------

   function First (Container : Set) return Cursor is
      Node : constant Count_Type := HT_Ops.First (Container.Content);

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

      -------------------------
      -- E_Elements_Included --
      -------------------------

      function E_Elements_Included
        (Left  : E.Sequence;
         Right : E.Sequence) return Boolean
      is
      begin
         for I in 1 .. E.Length (Left) loop
            if not E.Contains (Right, 1, E.Length (Right), E.Get (Left, I))
            then
               return False;
            end if;
         end loop;

         return True;
      end E_Elements_Included;

      function E_Elements_Included
        (Left  : E.Sequence;
         Model : M.Set;
         Right : E.Sequence) return Boolean
      is
      begin
         for I in 1 .. E.Length (Left) loop
            declare
               Item : constant Element_Type := E.Get (Left, I);
            begin
               if M.Contains (Model, Item) then
                  if not E.Contains (Right, 1, E.Length (Right), Item) then
                     return False;
                  end if;
               end if;
            end;
         end loop;

         return True;
      end E_Elements_Included;

      function E_Elements_Included
        (Container : E.Sequence;
         Model     : M.Set;
         Left      : E.Sequence;
         Right     : E.Sequence) return Boolean
      is
      begin
         for I in 1 .. E.Length (Container) loop
            declare
               Item : constant Element_Type := E.Get (Container, I);
            begin
               if M.Contains (Model, Item) then
                  if not E.Contains (Left, 1, E.Length (Left), Item) then
                     return False;
                  end if;
               else
                  if not E.Contains (Right, 1, E.Length (Right), Item) then
                     return False;
                  end if;
               end if;
            end;
         end loop;

         return True;
      end E_Elements_Included;

      --------------
      -- Elements --
      --------------

      function Elements (Container : Set) return E.Sequence is
         Position : Count_Type := HT_Ops.First (Container.Content);
         R        : E.Sequence;

      begin
         --  Can't use First, Next or Element here, since they depend on models
         --  for their postconditions.

         while Position /= 0 loop
            R := E.Add (R, Container.Content.Nodes (Position).Element);
            Position := HT_Ops.Next (Container.Content, Position);
         end loop;

         return R;
      end Elements;

      ----------
      -- Find --
      ----------

      function Find
        (Container : E.Sequence;
         Item      : Element_Type) return Count_Type
      is
      begin
         for I in 1 .. E.Length (Container) loop
            if Equivalent_Elements (Item, E.Get (Container, I)) then
               return I;
            end if;
         end loop;
         return 0;
      end Find;

      ----------------------------
      -- Lift_Abstraction_Level --
      ----------------------------

      procedure Lift_Abstraction_Level (Container : Set) is null;

      -----------------------
      -- Mapping_Preserved --
      -----------------------

      function Mapping_Preserved
        (E_Left  : E.Sequence;
         E_Right : E.Sequence;
         P_Left  : P.Map;
         P_Right : P.Map) return Boolean
      is
      begin
         for C of P_Left loop
            if not P.Has_Key (P_Right, C)
              or else P.Get (P_Left,  C) > E.Length (E_Left)
              or else P.Get (P_Right, C) > E.Length (E_Right)
              or else E.Get (E_Left,  P.Get (P_Left,  C)) /=
                      E.Get (E_Right, P.Get (P_Right, C))
            then
               return False;
            end if;
         end loop;

         return True;
      end Mapping_Preserved;

      ------------------------------
      -- Mapping_Preserved_Except --
      ------------------------------

      function Mapping_Preserved_Except
        (E_Left   : E.Sequence;
         E_Right  : E.Sequence;
         P_Left   : P.Map;
         P_Right  : P.Map;
         Position : Cursor) return Boolean
      is
      begin
         for C of P_Left loop
            if C /= Position
              and (not P.Has_Key (P_Right, C)
                    or else P.Get (P_Left,  C) > E.Length (E_Left)
                    or else P.Get (P_Right, C) > E.Length (E_Right)
                    or else E.Get (E_Left,  P.Get (P_Left,  C)) /=
                            E.Get (E_Right, P.Get (P_Right, C)))
            then
               return False;
            end if;
         end loop;

         return True;
      end Mapping_Preserved_Except;

      -----------
      -- Model --
      -----------

      function Model (Container : Set) return M.Set is
         Position : Count_Type := HT_Ops.First (Container.Content);
         R        : M.Set;

      begin
         --  Can't use First, Next or Element here, since they depend on models
         --  for their postconditions.

         while Position /= 0 loop
            R :=
              M.Add
                (Container => R,
                 Item      => Container.Content.Nodes (Position).Element);

            Position := HT_Ops.Next (Container.Content, Position);
         end loop;

         return R;
      end Model;

      ---------------
      -- Positions --
      ---------------

      function Positions (Container : Set) return P.Map is
         I        : Count_Type := 1;
         Position : Count_Type := HT_Ops.First (Container.Content);
         R        : P.Map;

      begin
         --  Can't use First, Next or Element here, since they depend on models
         --  for their postconditions.

         while Position /= 0 loop
            R := P.Add (R, (Node => Position), I);
            pragma Assert (P.Length (R) = Big (I));
            Position := HT_Ops.Next (Container.Content, Position);
            I := I + 1;
         end loop;

         return R;
      end Positions;

   end Formal_Model;

   ----------
   -- Free --
   ----------

   procedure Free (HT : in out Set; X : Count_Type) is
   begin
      if X /= 0 then
         pragma Assert (X <= HT.Capacity);
         HT.Content.Nodes (X).Has_Element := False;
         HT_Ops.Free (HT.Content, X);
      end if;
   end Free;

   ----------------------
   -- Generic_Allocate --
   ----------------------

   procedure Generic_Allocate
     (HT   : in out Hash_Table_Type;
      Node : out Count_Type)
   is
      procedure Allocate is new HT_Ops.Generic_Allocate (Set_Element);
   begin
      Allocate (HT, Node);
      HT.Nodes (Node).Has_Element := True;
   end Generic_Allocate;

   package body Generic_Keys with SPARK_Mode => Off is

      -----------------------
      -- Local Subprograms --
      -----------------------

      function Equivalent_Key_Node
        (Key  : Key_Type;
         Node : Node_Type) return Boolean;
      pragma Inline (Equivalent_Key_Node);

      --------------------------
      -- Local Instantiations --
      --------------------------

      package Key_Keys is new Hash_Tables.Generic_Formal_Keys
        (HT_Types        => HT_Types,
         Next            => Next,
         Set_Next        => Set_Next,
         Key_Type        => Key_Type,
         Hash            => Hash,
         Equivalent_Keys => Equivalent_Key_Node);

      --------------
      -- Contains --
      --------------

      function Contains
        (Container : Set;
         Key       : Key_Type) return Boolean
      is
      begin
         return Find (Container, Key) /= No_Element;
      end Contains;

      ------------
      -- Delete --
      ------------

      procedure Delete (Container : in out Set; Key : Key_Type) is
         X : Count_Type;

      begin
         Key_Keys.Delete_Key_Sans_Free (Container.Content, Key, X);

         if X = 0 then
            raise Constraint_Error with "attempt to delete key not in set";
         end if;

         Free (Container, X);
      end Delete;

      -------------
      -- Element --
      -------------

      function Element
        (Container : Set;
         Key       : Key_Type) return Element_Type
      is
         Node : constant Count_Type := Find (Container, Key).Node;

      begin
         if Node = 0 then
            raise Constraint_Error with "key not in map";
         end if;

         return Container.Content.Nodes (Node).Element;
      end Element;

      -------------------------
      -- Equivalent_Key_Node --
      -------------------------

      function Equivalent_Key_Node
        (Key  : Key_Type;
         Node : Node_Type) return Boolean
      is
      begin
         return Equivalent_Keys (Key, Generic_Keys.Key (Node.Element));
      end Equivalent_Key_Node;

      -------------
      -- Exclude --
      -------------

      procedure Exclude (Container : in out Set; Key : Key_Type) is
         X : Count_Type;
      begin
         Key_Keys.Delete_Key_Sans_Free (Container.Content, Key, X);
         Free (Container, X);
      end Exclude;

      ----------
      -- Find --
      ----------

      function Find
        (Container : Set;
         Key       : Key_Type) return Cursor
      is
         Node : constant Count_Type := Key_Keys.Find (Container.Content, Key);
      begin
         return (if Node = 0 then No_Element else (Node => Node));
      end Find;

      ------------------
      -- Formal_Model --
      ------------------

      package body Formal_Model is

         -----------------------
         -- M_Included_Except --
         -----------------------

         function M_Included_Except
           (Left  : M.Set;
            Right : M.Set;
            Key   : Key_Type) return Boolean
         is
         begin
            for E of Left loop
               if not Contains (Right, E)
                 and not Equivalent_Keys (Generic_Keys.Key (E), Key)
               then
                  return False;
               end if;
            end loop;

            return True;
         end M_Included_Except;

      end Formal_Model;

      ---------
      -- Key --
      ---------

      function Key (Container : Set; Position : Cursor) return Key_Type is
      begin
         if not Has_Element (Container, Position) then
            raise Constraint_Error with "Position cursor has no element";
         end if;

         pragma Assert
           (Vet (Container, Position), "bad cursor in function Key");

         declare
            N : Node_Type renames Container.Content.Nodes (Position.Node);
         begin
            return Key (N.Element);
         end;
      end Key;

      -------------
      -- Replace --
      -------------

      procedure Replace
        (Container : in out Set;
         Key       : Key_Type;
         New_Item  : Element_Type)
      is
         Node : constant Count_Type := Key_Keys.Find (Container.Content, Key);

      begin
         if Node = 0 then
            raise Constraint_Error with "attempt to replace key not in set";
         end if;

         Replace_Element (Container.Content, Node, New_Item);
      end Replace;

   end Generic_Keys;

   -----------------
   -- Has_Element --
   -----------------

   function Has_Element (Container : Set; Position : Cursor) return Boolean is
   begin
      if Position.Node = 0
        or else not Container.Content.Nodes (Position.Node).Has_Element
      then
         return False;
      end if;

      return True;
   end Has_Element;

   ---------------
   -- Hash_Node --
   ---------------

   function Hash_Node (Node : Node_Type) return Hash_Type is
   begin
      return Hash (Node.Element);
   end Hash_Node;

   -------------
   -- Include --
   -------------

   procedure Include (Container : in out Set; New_Item : Element_Type) is
      Inserted : Boolean;
      Position : Cursor;

   begin
      Insert (Container, New_Item, Position, Inserted);

      if not Inserted then
         Container.Content.Nodes (Position.Node).Element := New_Item;
      end if;
   end Include;

   ------------
   -- Insert --
   ------------

   procedure Insert
     (Container : in out Set;
      New_Item  : Element_Type;
      Position  : out Cursor;
      Inserted  : out Boolean)
   is
   begin
      Insert (Container, New_Item, Position.Node, Inserted);
   end Insert;

   procedure Insert (Container : in out Set; New_Item : Element_Type) is
      Inserted        : Boolean;
      Unused_Position : Cursor;

   begin
      Insert (Container, New_Item, Unused_Position, Inserted);

      if not Inserted then
         raise Constraint_Error with
           "attempt to insert element already in set";
      end if;
   end Insert;

   procedure Insert
     (Container : in out Set;
      New_Item  : Element_Type;
      Node      : out Count_Type;
      Inserted  : out Boolean)
   is
      procedure Allocate_Set_Element (Node : in out Node_Type);
      pragma Inline (Allocate_Set_Element);

      procedure New_Node
        (HT   : in out Hash_Table_Type;
         Node : out Count_Type);
      pragma Inline (New_Node);

      procedure Local_Insert is
        new Element_Keys.Generic_Conditional_Insert (New_Node);

      procedure Allocate is
        new Generic_Allocate (Allocate_Set_Element);

      ---------------------------
      --  Allocate_Set_Element --
      ---------------------------

      procedure Allocate_Set_Element (Node : in out Node_Type) is
      begin
         Node.Element := New_Item;
      end Allocate_Set_Element;

      --------------
      -- New_Node --
      --------------

      procedure New_Node
        (HT   : in out Hash_Table_Type;
         Node : out Count_Type)
      is
      begin
         Allocate (HT, Node);
      end New_Node;

   --  Start of processing for Insert

   begin
      Local_Insert (Container.Content, New_Item, Node, Inserted);
   end Insert;

   ------------------
   -- Intersection --
   ------------------

   procedure Intersection (Target : in out Set; Source : Set) is
      Tgt_Node : Count_Type;
      TN       : Nodes_Type renames Target.Content.Nodes;

   begin
      if Source.Content.Length = 0 then
         Clear (Target);
         return;
      end if;

      Tgt_Node := HT_Ops.First (Target.Content);
      while Tgt_Node /= 0 loop
         if Find (Source, TN (Tgt_Node).Element).Node /= 0 then
            Tgt_Node := HT_Ops.Next (Target.Content, Tgt_Node);

         else
            declare
               X : constant Count_Type := Tgt_Node;
            begin
               Tgt_Node := HT_Ops.Next (Target.Content, Tgt_Node);
               HT_Ops.Delete_Node_Sans_Free (Target.Content, X);
               Free (Target, X);
            end;
         end if;
      end loop;
   end Intersection;

   procedure Intersection (Left : Set; Right : Set; Target : in out Set) is
      procedure Process (L_Node : Count_Type);

      procedure Iterate is
        new HT_Ops.Generic_Iteration (Process);

      -------------
      -- Process --
      -------------

      procedure Process (L_Node : Count_Type) is
         E        : Element_Type renames Left.Content.Nodes (L_Node).Element;
         Unused_X : Count_Type;
         B        : Boolean;

      begin
         if Find (Right, E).Node /= 0 then
            Insert (Target, E, Unused_X, B);
            pragma Assert (B);
         end if;
      end Process;

   --  Start of processing for Intersection

   begin
      Iterate (Left.Content);
   end Intersection;

   function Intersection (Left : Set; Right : Set) return Set is
      C : constant Count_Type :=
        Count_Type'Min (Length (Left), Length (Right));  -- ???
      H : constant Hash_Type := Default_Modulus (C);

   begin
      return S : Set (C, H) do
         if Length (Left) /= 0 and Length (Right) /= 0 then
            Intersection (Left, Right, Target => S);
         end if;
      end return;
   end Intersection;

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (Container : Set) return Boolean is
   begin
      return Length (Container) = 0;
   end Is_Empty;

   -----------
   -- Is_In --
   -----------

   function Is_In (HT : Set; Key : Node_Type) return Boolean is
   begin
      return Element_Keys.Find (HT.Content, Key.Element) /= 0;
   end Is_In;

   ---------------
   -- Is_Subset --
   ---------------

   function Is_Subset (Subset : Set; Of_Set : Set) return Boolean is
      Subset_Node  : Count_Type;
      Subset_Nodes : Nodes_Type renames Subset.Content.Nodes;

   begin
      if Length (Subset) > Length (Of_Set) then
         return False;
      end if;

      Subset_Node := First (Subset).Node;
      while Subset_Node /= 0 loop
         declare
            S : constant Count_Type := Subset_Node;
            N : Node_Type renames Subset_Nodes (S);
            E : Element_Type renames N.Element;

         begin
            if Find (Of_Set, E).Node = 0 then
               return False;
            end if;
         end;

         Subset_Node := HT_Ops.Next (Subset.Content, Subset_Node);
      end loop;

      return True;
   end Is_Subset;

   ------------
   -- Length --
   ------------

   function Length (Container : Set) return Count_Type is
   begin
      return Container.Content.Length;
   end Length;

   ----------
   -- Move --
   ----------

   --  Comments???

   procedure Move (Target : in out Set; Source : in out Set) is
      NN   : HT_Types.Nodes_Type renames Source.Content.Nodes;
      X, Y : Count_Type;

   begin
      if Target.Capacity < Length (Source) then
         raise Constraint_Error with  -- ???
           "Source length exceeds Target capacity";
      end if;

      Clear (Target);

      if Source.Content.Length = 0 then
         return;
      end if;

      X := HT_Ops.First (Source.Content);
      while X /= 0 loop
         Insert (Target, NN (X).Element);  -- optimize???

         Y := HT_Ops.Next (Source.Content, X);

         HT_Ops.Delete_Node_Sans_Free (Source.Content, X);
         Free (Source, X);

         X := Y;
      end loop;
   end Move;

   ----------
   -- Next --
   ----------

   function Next (Node : Node_Type) return Count_Type is
   begin
      return Node.Next;
   end Next;

   function Next (Container : Set; Position : Cursor) return Cursor is
   begin
      if Position.Node = 0 then
         return No_Element;
      end if;

      if not Has_Element (Container, Position) then
         raise Constraint_Error with "Position has no element";
      end if;

      pragma Assert (Vet (Container, Position), "bad cursor in Next");

      return (Node => HT_Ops.Next (Container.Content, Position.Node));
   end Next;

   procedure Next (Container : Set; Position : in out Cursor) is
   begin
      Position := Next (Container, Position);
   end Next;

   -------------
   -- Overlap --
   -------------

   function Overlap (Left, Right : Set) return Boolean is
      Left_Node  : Count_Type;
      Left_Nodes : Nodes_Type renames Left.Content.Nodes;

   begin
      if Length (Right) = 0 or Length (Left) = 0 then
         return False;
      end if;

      Left_Node := First (Left).Node;
      while Left_Node /= 0 loop
         declare
            L : constant Count_Type := Left_Node;
            N : Node_Type renames Left_Nodes (L);
            E : Element_Type renames N.Element;
         begin
            if Find (Right, E).Node /= 0 then
               return True;
            end if;
         end;

         Left_Node := HT_Ops.Next (Left.Content, Left_Node);
      end loop;

      return False;
   end Overlap;

   -------------
   -- Replace --
   -------------

   procedure Replace (Container : in out Set; New_Item : Element_Type) is
      Node : constant Count_Type :=
        Element_Keys.Find (Container.Content, New_Item);

   begin
      if Node = 0 then
         raise Constraint_Error with "attempt to replace element not in set";
      end if;

      Container.Content.Nodes (Node).Element := New_Item;
   end Replace;

   ---------------------
   -- Replace_Element --
   ---------------------

   procedure Replace_Element
     (Container : in out Set;
      Position  : Cursor;
      New_Item  : Element_Type)
   is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with "Position cursor equals No_Element";
      end if;

      pragma Assert
        (Vet (Container, Position), "bad cursor in Replace_Element");

      Replace_Element (Container.Content, Position.Node, New_Item);
   end Replace_Element;

   ----------------------
   -- Reserve_Capacity --
   ----------------------

   procedure Reserve_Capacity
     (Container : in out Set;
      Capacity  : Count_Type)
   is
   begin
      if Capacity > Container.Capacity then
         raise Constraint_Error with "requested capacity is too large";
      end if;
   end Reserve_Capacity;

   ------------------
   --  Set_Element --
   ------------------

   procedure Set_Element (Node : in out Node_Type; Item : Element_Type) is
   begin
      Node.Element := Item;
   end Set_Element;

   --------------
   -- Set_Next --
   --------------

   procedure Set_Next (Node : in out Node_Type; Next : Count_Type) is
   begin
      Node.Next := Next;
   end Set_Next;

   --------------------------
   -- Symmetric_Difference --
   --------------------------

   procedure Symmetric_Difference (Target : in out Set; Source : Set) is
      procedure Process (Source_Node : Count_Type);
      pragma Inline (Process);

      procedure Iterate is new HT_Ops.Generic_Iteration (Process);

      -------------
      -- Process --
      -------------

      procedure Process (Source_Node : Count_Type) is
         B        : Boolean;
         N        : Node_Type renames Source.Content.Nodes (Source_Node);
         Unused_X : Count_Type;

      begin
         if Is_In (Target, N) then
            Delete (Target, N.Element);
         else
            Insert (Target, N.Element, Unused_X, B);
            pragma Assert (B);
         end if;
      end Process;

   --  Start of processing for Symmetric_Difference

   begin
      if Length (Target) = 0 then
         Assign (Target, Source);
         return;
      end if;

      Iterate (Source.Content);
   end Symmetric_Difference;

   function Symmetric_Difference (Left : Set; Right : Set) return Set is
   begin
      if Length (Right) = 0 then
         return Copy (Left);
      end if;

      if Length (Left) = 0 then
         return Copy (Right);
      end if;

      declare
         C : constant Count_Type := Length (Left) + Length (Right);
         H : constant Hash_Type := Default_Modulus (C);
      begin
         return S : Set (C, H) do
            Difference (Left, Right, S);
            Difference (Right, Left, S);
         end return;
      end;
   end Symmetric_Difference;

   ------------
   -- To_Set --
   ------------

   function To_Set (New_Item : Element_Type) return Set is
      Unused_X : Count_Type;
      B        : Boolean;

   begin
      return S : Set (Capacity => 1, Modulus => 1) do
         Insert (S, New_Item, Unused_X, B);
         pragma Assert (B);
      end return;
   end To_Set;

   -----------
   -- Union --
   -----------

   procedure Union (Target : in out Set; Source : Set) is
      procedure Process (Src_Node : Count_Type);

      procedure Iterate is
        new HT_Ops.Generic_Iteration (Process);

      -------------
      -- Process --
      -------------

      procedure Process (Src_Node : Count_Type) is
         N : Node_Type renames Source.Content.Nodes (Src_Node);
         E : Element_Type renames N.Element;

         Unused_X : Count_Type;
         Unused_B : Boolean;

      begin
         Insert (Target, E, Unused_X, Unused_B);
      end Process;

   --  Start of processing for Union

   begin
      Iterate (Source.Content);
   end Union;

   function Union (Left : Set; Right : Set) return Set is
   begin
      if Length (Right) = 0 then
         return Copy (Left);
      end if;

      if Length (Left) = 0 then
         return Copy (Right);
      end if;

      declare
         C : constant Count_Type := Length (Left) + Length (Right);
         H : constant Hash_Type := Default_Modulus (C);
      begin
         return S : Set (C, H) do
            Assign (Target => S, Source => Left);
            Union (Target => S, Source => Right);
         end return;
      end;
   end Union;

   ---------
   -- Vet --
   ---------

   function Vet (Container : Set; Position : Cursor) return Boolean is
   begin
      if not Container_Checks'Enabled then
         return True;
      end if;

      if Position.Node = 0 then
         return True;
      end if;

      declare
         S : Set renames Container;
         N : Nodes_Type renames S.Content.Nodes;
         X : Count_Type;

      begin
         if S.Content.Length = 0 then
            return False;
         end if;

         if Position.Node > N'Last then
            return False;
         end if;

         if N (Position.Node).Next = Position.Node then
            return False;
         end if;

         X := S.Content.Buckets
           (Element_Keys.Index (S.Content, N (Position.Node).Element));

         for J in 1 .. S.Content.Length loop
            if X = Position.Node then
               return True;
            end if;

            if X = 0 then
               return False;
            end if;

            if X = N (X).Next then  --  to prevent unnecessary looping
               return False;
            end if;

            X := N (X).Next;
         end loop;

         return False;
      end;
   end Vet;

end SPARK.Containers.Formal.Hashed_Sets;
