------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--               SPARK.CONTAINERS.FORMAL.UNBOUNDED_HASHED_SETS              --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--          Copyright (C) 2022-2023, Free Software Foundation, Inc.         --
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

with Ada.Unchecked_Deallocation;

with System; use type System.Address;

package body SPARK.Containers.Formal.Unbounded_Hashed_Sets with
  SPARK_Mode => Off
is
   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Difference (Left : Set; Right : Set; Target : in out Set);
   --  Inserts all the elements of Left that are not in Right in Target

   function Equivalent_Keys
     (Key  : Element_Type;
      Node : Node_Type) return Boolean;
   --  Test if Node has the key Key using the function provided as a generic
   --  parameter.

   pragma Inline (Equivalent_Keys);

   procedure Free
     (HT : in out Set;
      X  : Count_Type);
   --  Cleanly remove a node from the Map and put it back in the free list

   generic
      with procedure Set_Element (Node : in out Node_Type);
   procedure Generic_Allocate
     (HT   : in out Hash_Table_Type;
      Node : out Count_Type);
   --  Allocate a new node i.e get it out of the free list

   function Hash_Node (Node : Node_Type) return Hash_Type;
   pragma Inline (Hash_Node);
   --  Hash the Node Element (which is also the key) using the Hash function
   --  provided as a generic parameter.

   procedure Insert
     (Container : in out Set;
      New_Item  : Element_Type;
      Node      : out Count_Type;
      Inserted  : out Boolean);
   --  Try to Insert New_Item in the Set. Node is the inserted node. Insert
   --  might fail if, for example, another element in the Set already got the
   --  same key. In this case, Node refer to this node and Inserted is False.

   procedure Intersection
     (Left   : Set;
      Right  : Set;
      Target : in out Set);
   --  Compute the Intersection between Left and Right and store it in Target

   function Is_In
     (HT  : Set;
      Key : Node_Type) return Boolean;
   --  Check if Node's element is in HT

   pragma Inline (Is_In);

   procedure Set_Element (Node : in out Node_Type; Item : Element_Type);
   pragma Inline (Set_Element);
   --  Set Node's Element

   function Next (Node : Node_Type) return Count_Type;
   pragma Inline (Next);
   --  Return the node following Node in the same Bucket. Used by Hash_Tables
   --  operation's functions.

   procedure Set_Next (Node : in out Node_Type; Next : Count_Type);
   pragma Inline (Set_Next);
   --  Set the node following Node. Useb by Hash_Tables operation's functions.

   function Vet (Container : Set; Position : Cursor) return Boolean
   --  Check if Position is correct in Container

     with Inline;

   procedure Resize (Container : in out Set; Size : Count_Type := 0) with
   --  Allocate a new larger Set

     Global => null,
     Post   =>
       Model (Container) = Model (Container)'Old
         and Length (Container) = Length (Container)'Old
         and Elements (Container) =  Elements (Container)'Old
         and Positions (Container) = Positions (Container)'Old;

   --------------------------
   -- Local Instantiations --
   --------------------------

   procedure Finalize_Content is new Ada.Unchecked_Deallocation
     (Object => HT_Types.Hash_Table_Type,
      Name   => HT_Access);
   --  Deallocate a HT_Types.Hash_Table_Type

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
                 Item      =>
                   Element (Left.Content.Nodes (Node).E_Holder)).Node;

            if ENode = 0
              or else Element (Right.Content.Nodes (ENode).E_Holder) /=
              Element (Left.Content.Nodes (Node).E_Holder)
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

   procedure Adjust (Source : in out Set) is
   begin
      if Source.Content = Empty_HT'Access then
         return;
      end if;

      declare
         New_Set : constant HT_Access := new HT_Types.Hash_Table_Type
           (Source.Content.Capacity, Source.Modulus);
      begin
         New_Set.Length := Source.Content.Length;
         New_Set.Free   := Source.Content.Free;

         --  Copy the nodes. The call to Adjust will make a proper copy of
         --  the holders.

         New_Set.Nodes (1 .. Source.Content.Capacity) :=
           Source.Content.Nodes (1 .. Source.Content.Capacity);

         --  There is no nodes to be added to the free list since Container and
         --  New_Map have the same size.

         --  Copy the buckets

         New_Set.Buckets (1 .. Source.Modulus) :=
           Source.Content.Buckets (1 .. Source.Modulus);

         --  Put the new Set in Source. Source.Content must not be finalize
         --  since we are doing an "Adjust". In fact, it still exist somewere
         --  else.

         Source.Content := New_Set;
      end;
   end Adjust;

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
         Insert (Target, Element (N.E_Holder), Unused_X, B);
         pragma Assert (B);
      end Insert_Element;

   --  Start of processing for Assign

   begin
      HT_Ops.Clear (Target.Content.all);
      Insert_Elements (Source.Content.all);
   end Assign;

   -----------
   -- Clear --
   -----------

   procedure Clear (Container : in out Set) is
   begin
      HT_Ops.Clear (Container.Content.all);
   end Clear;

   ------------------------
   -- Constant_Reference --
   ------------------------

   function Constant_Reference
     (Container : Set;
      Position  : Cursor) return not null access constant Element_Type
   is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with "Position cursor equals No_Element";
      end if;

      pragma Assert
        (Vet (Container, Position), "bad cursor in function Element");

      return Element_Access (Container.Content.Nodes (Position.Node).E_Holder);
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

   function Copy (Source : Set) return Set
   is
      Target : Set (Source.Modulus);

   begin
      if Source.Content = Empty_HT'Access then
         return Target;
      end if;

      --  The implicit call to Adjust will properly copy the element

      Target.Content := new Hash_Table_Type'(Source.Content.all);

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
      Element_Keys.Delete_Key_Sans_Free (Container.Content.all, Item, X);

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

      HT_Ops.Delete_Node_Sans_Free (Container.Content.all, Position.Node);
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
         Tgt_Node := HT_Ops.First (Target.Content.all);
         while Tgt_Node /= 0 loop
            if Element_Keys.Find
                 (Source.Content.all, Element (TN (Tgt_Node).E_Holder)) /= 0
            then
               declare
                  X : constant Count_Type := Tgt_Node;
               begin
                  Tgt_Node := HT_Ops.Next (Target.Content.all, Tgt_Node);
                  HT_Ops.Delete_Node_Sans_Free (Target.Content.all, X);
                  Free (Target, X);
               end;

            else
               Tgt_Node := HT_Ops.Next (Target.Content.all, Tgt_Node);
            end if;
         end loop;

         return;
      else
         Src_Node := HT_Ops.First (Source.Content.all);
         Src_Last := 0;
      end if;

      while Src_Node /= Src_Last loop
         Tgt_Node := Element_Keys.Find
           (Target.Content.all, Element (SN (Src_Node).E_Holder));

         if Tgt_Node /= 0 then
            HT_Ops.Delete_Node_Sans_Free (Target.Content.all, Tgt_Node);
            Free (Target, Tgt_Node);
         end if;

         Src_Node := HT_Ops.Next (Source.Content.all, Src_Node);
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
         E        : constant Element_Type :=
           Element (Left.Content.Nodes (L_Node).E_Holder);
         Unused_X : Count_Type;

      begin
         if Find (Right, E).Node = 0 then
            Insert (Target, E, Unused_X, B);
            pragma Assert (B);
         end if;
      end Process;

   --  Start of processing for Difference

   begin
      Iterate (Left.Content.all);
   end Difference;

   function Difference (Left : Set; Right : Set) return Set is
   begin
      if Length (Left) = 0 then
         return Empty_Set (Modulus => Left.Modulus);
      end if;

      if Length (Right) = 0 then
         return Copy (Left);
      end if;

      declare
         C : constant Count_Type := Length (Left);
         H : constant Hash_Type  := Default_Modulus (C);
      begin
         return S : Set (H) do
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

      return Element (Container.Content.Nodes (Position.Node).E_Holder);
   end Element;

   ---------------
   -- Empty_Set --
   ---------------

   function Empty_Set (Modulus : Hash_Type := 0) return Set is
   begin
      return (Ada.Finalization.Controlled with Modulus => Modulus,
                                               Content => Empty_HT'Access);
   end Empty_Set;

   ---------------------
   -- Equivalent_Keys --
   ---------------------

   function Equivalent_Keys
     (Key  : Element_Type;
      Node : Node_Type) return Boolean
   is
   begin
      return Equivalent_Elements (Key, Element (Node.E_Holder));
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
                     Element_Keys.Index (R_HT, Element (L_Node.E_Holder));
         R_Node  : Count_Type := R_HT.Buckets (R_Index);
         RN      : Nodes_Type renames R_HT.Nodes;

      begin
         loop
            if R_Node = 0 then
               return False;
            end if;

            if Equivalent_Elements
                 (Element (L_Node.E_Holder), Element (RN (R_Node).E_Holder))
            then
               return True;
            end if;

            R_Node := HT_Ops.Next (R_HT, R_Node);
         end loop;
      end Find_Equivalent_Key;

   --  Start of processing for Equivalent_Sets

   begin
      return Is_Equivalent (Left.Content.all, Right.Content.all);
   end Equivalent_Sets;

   -------------
   -- Exclude --
   -------------

   procedure Exclude (Container : in out Set; Item : Element_Type) is
      X : Count_Type;
   begin
      Element_Keys.Delete_Key_Sans_Free (Container.Content.all, Item, X);
      Free (Container, X);
   end Exclude;

   --------------
   -- Finalize --
   --------------

   procedure Finalize (Container : in out Set) is
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

   function Find
     (Container : Set;
      Item      : Element_Type) return Cursor
   is
      Node : constant Count_Type :=
        Element_Keys.Find (Container.Content.all, Item);

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

      ----------------------
      -- E_Elements_Equal --
      ----------------------

      function E_Elements_Equal
        (Left  : E.Sequence;
         Right : E.Sequence) return Boolean
      is
      begin
         for I in 1 .. E.Last (Left) loop
            if not E.Contains (Right, 1, E.Last (Right), E.Get (Left, I))
            then
               return False;
            end if;
         end loop;

         return True;
      end E_Elements_Equal;

      -------------------------
      -- E_Elements_Included --
      -------------------------

      function E_Elements_Included
        (Left  : E.Sequence;
         Right : E.Sequence) return Boolean
      is
      begin
         for I in 1 .. E.Last (Left) loop
            declare
               J : constant Count_Type := E.Find (Right, E.Get (Left, I));
            begin
               if J = 0
                 or else not Element_Logic_Equal
                   (E.Get (Left, I), E.Get (Right, J))
               then
                  return False;
               end if;
            end;
         end loop;

         return True;
      end E_Elements_Included;

      function E_Elements_Included
        (Left  : E.Sequence;
         Model : M.Set;
         Right : E.Sequence) return Boolean
      is
      begin
         for I in 1 .. E.Last (Left) loop
            declare
               Item : constant Element_Type := E.Get (Left, I);
            begin
               if M.Contains (Model, Item) then
                  declare
                     J : constant Count_Type :=
                       E.Find (Right, E.Get (Left, I));
                  begin
                     if J = 0
                       or else not Element_Logic_Equal (Item, E.Get (Right, J))
                     then
                        return False;
                     end if;
                  end;
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
         for I in 1 .. E.Last (Container) loop
            declare
               Item : constant Element_Type := E.Get (Container, I);
            begin
               if M.Contains (Model, Item) then
                  declare
                     J : constant Count_Type :=
                       E.Find (Left, E.Get (Container, I));
                  begin
                     if J = 0
                       or else not Element_Logic_Equal (Item, E.Get (Left, J))
                     then
                        return False;
                     end if;
                  end;
               else
                  declare
                     J : constant Count_Type :=
                       E.Find (Right, E.Get (Container, I));
                  begin
                     if J = 0
                       or else not Element_Logic_Equal (Item, E.Get (Right, J))
                     then
                        return False;
                     end if;
                  end;
               end if;
            end;
         end loop;

         return True;
      end E_Elements_Included;

      -------------------------
      -- Element_Logic_Equal --
      -------------------------

      function Element_Logic_Equal (Left, Right : Element_Type) return Boolean
      is
      begin
         Check_Or_Fail;
         return Left = Right;
      end Element_Logic_Equal;

      --------------
      -- Elements --
      --------------

      function Elements (Container : Set) return E.Sequence is
         Position : Count_Type := HT_Ops.First (Container.Content.all);
         R        : E.Sequence;

      begin
         --  Can't use First, Next or Element here, since they depend on models
         --  for their postconditions.

         while Position /= 0 loop
            R :=
              E.Add (R, Element (Container.Content.Nodes (Position).E_Holder));
            Position := HT_Ops.Next (Container.Content.all, Position);
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
         for I in 1 .. E.Last (Container) loop
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
              or else P.Get (P_Left,  C) > E.Last (E_Left)
              or else P.Get (P_Right, C) > E.Last (E_Right)
              or else not Element_Logic_Equal
                (E.Get (E_Left,  P.Get (P_Left,  C)),
                 E.Get (E_Right, P.Get (P_Right, C)))
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
                    or else P.Get (P_Left,  C) > E.Last (E_Left)
                    or else P.Get (P_Right, C) > E.Last (E_Right)
                    or else not Element_Logic_Equal
                     (E.Get (E_Left,  P.Get (P_Left,  C)),
                      E.Get (E_Right, P.Get (P_Right, C))))
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
         Position : Count_Type := HT_Ops.First (Container.Content.all);
         R        : M.Set;

      begin
         --  Can't use First, Next or Element here, since they depend on models
         --  for their postconditions.

         while Position /= 0 loop
            R :=
              M.Add
                (Container => R,
                 Item      => Element
                                (Container.Content.Nodes (Position).E_Holder));

            Position := HT_Ops.Next (Container.Content.all, Position);
         end loop;

         return R;
      end Model;

      ---------------
      -- Positions --
      ---------------

      function Positions (Container : Set) return P.Map is
         I        : Count_Type := 1;
         Position : Count_Type := HT_Ops.First (Container.Content.all);
         R        : P.Map;

      begin
         --  Can't use First, Next or Element here, since they depend on models
         --  for their postconditions.

         while Position /= 0 loop
            R := P.Add (R, (Node => Position), I);
            pragma Assert (P.Length (R) = E.Big (I));
            Position := HT_Ops.Next (Container.Content.all, Position);
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
      if HT.Content = Empty_HT'Access then
         return;
      end if;

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
         Key_Keys.Delete_Key_Sans_Free (Container.Content.all, Key, X);

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

         return Element (Container.Content.Nodes (Node).E_Holder);
      end Element;

      -------------------------
      -- Equivalent_Key_Node --
      -------------------------

      function Equivalent_Key_Node
        (Key  : Key_Type;
         Node : Node_Type) return Boolean
      is
      begin
         return Equivalent_Keys
                  (Key, Generic_Keys.Key (Element (Node.E_Holder)));
      end Equivalent_Key_Node;

      -------------
      -- Exclude --
      -------------

      procedure Exclude (Container : in out Set; Key : Key_Type) is
         X : Count_Type;
      begin
         Key_Keys.Delete_Key_Sans_Free (Container.Content.all, Key, X);
         Free (Container, X);
      end Exclude;

      ----------
      -- Find --
      ----------

      function Find
        (Container : Set;
         Key       : Key_Type) return Cursor
      is
         Node : constant Count_Type :=
           Key_Keys.Find (Container.Content.all, Key);
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
            return Key (Element (N.E_Holder));
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
         Node : constant Count_Type :=
           Key_Keys.Find (Container.Content.all, Key);

      begin
         if Node = 0 then
            raise Constraint_Error with "attempt to replace key not in set";
         end if;

         Replace_Element (Container.Content.all, Node, New_Item);
      end Replace;

   end Generic_Keys;

   -----------------
   -- Has_Element --
   -----------------

   function Has_Element (Container : Set; Position : Cursor) return Boolean is
   begin
      if Position.Node = 0
        or else Position.Node < 1
        or else Position.Node > Container.Content.Capacity
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
      return Hash (Element (Node.E_Holder));
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
         Replace_Element
           (Container.Content.Nodes (Position.Node).E_Holder, New_Item);
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
         Replace_Element (Node.E_Holder, New_Item);
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
      if Length (Container) = Container.Content.Capacity then
         Resize (Container);
      end if;

      Local_Insert (Container.Content.all, New_Item, Node, Inserted);
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

      Tgt_Node := HT_Ops.First (Target.Content.all);
      while Tgt_Node /= 0 loop
         if Find (Source, Element (TN (Tgt_Node).E_Holder)).Node /= 0 then
            Tgt_Node := HT_Ops.Next (Target.Content.all, Tgt_Node);

         else
            declare
               X : constant Count_Type := Tgt_Node;
            begin
               Tgt_Node := HT_Ops.Next (Target.Content.all, Tgt_Node);
               HT_Ops.Delete_Node_Sans_Free (Target.Content.all, X);
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
         E        : constant Element_Type :=
           Element (Left.Content.Nodes (L_Node).E_Holder);
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
      Iterate (Left.Content.all);
   end Intersection;

   function Intersection (Left : Set; Right : Set) return Set is
      H : constant Hash_Type :=
        Default_Modulus (Count_Type'Min (Length (Left), Length (Right)));

   begin
      return S : Set (H) do
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
      return Element_Keys.Find (HT.Content.all, Element (Key.E_Holder)) /= 0;
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

      --  Loop on Subset to check whether all the elements od Subset are in
      --  Of_Set or not.

      Subset_Node := First (Subset).Node;
      while Subset_Node /= 0 loop
         declare
            S : constant Count_Type := Subset_Node;
            N : Node_Type renames Subset_Nodes (S);
            E : Element_Type renames Element (N.E_Holder);

         begin
            if Find (Of_Set, E).Node = 0 then

               --  Node's elment is in Subset but not in Of_Set

               return False;
            end if;
         end;

         Subset_Node := HT_Ops.Next (Subset.Content.all, Subset_Node);
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

   procedure Move (Target : in out Set; Source : in out Set) is
   begin

      --  The move operation can be done by transferring the ownership of the
      --  Content (the underlying Hash_Table_Type) from Source to Target.
      --
      --  Finalize the Content of Target if necessary. It is not necessary to
      --  Finalize the elements since the Holder type is Controlled.

      Finalize (Target);

      Target.Content := Source.Content;
      Source.Content := Empty_HT'Access; --  Avoid sharing
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

      return (Node => HT_Ops.Next (Container.Content.all, Position.Node));
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

      --  Loop over Left to check whether at least one of its element is also
      --  in Right or not.

      Left_Node := First (Left).Node;
      while Left_Node /= 0 loop
         declare
            L : constant Count_Type := Left_Node;
            N : Node_Type renames Left_Nodes (L);
            E : Element_Type renames Element (N.E_Holder);
         begin
            if Find (Right, E).Node /= 0 then
               return True;
            end if;
         end;

         Left_Node := HT_Ops.Next (Left.Content.all, Left_Node);
      end loop;

      return False;
   end Overlap;

   -------------
   -- Replace --
   -------------

   procedure Replace (Container : in out Set; New_Item : Element_Type) is
      Node : constant Count_Type :=
        Element_Keys.Find (Container.Content.all, New_Item);

   begin
      if Node = 0 then
         raise Constraint_Error with "attempt to replace element not in set";
      end if;

      Replace_Element (Container.Content.Nodes (Node).E_Holder, New_Item);
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

      Replace_Element (Container.Content.all, Position.Node, New_Item);
   end Replace_Element;

   ------------
   -- Resize --
   ------------

   procedure Resize (Container : in out Set; Size : Count_Type := 0) is
      Min_Size : constant Count_Type := 100;
      New_Size : constant Count_Type := Count_Type'Max (Min_Size, Size);

      CC : HT_Access renames Container.Content;

   begin
      if CC = Empty_HT'Access then
         CC := new HT_Types.Hash_Table_Type (New_Size, Container.Modulus);
         return;
      end if;

      if CC.Nodes'Length = Count_Type'Last then
         raise Constraint_Error with "Set already at max size";
      end if;

      if Size /= 0 and then CC.Capacity >= Size then
         return;
      end if;

      declare
         Next_Size : constant Count_Type :=
           (if CC.Nodes'Length < Count_Type'Last / 2
            then 2 * CC.Nodes'Length
            else Count_Type'Last);
         New_Set : constant HT_Access :=
           new HT_Types.Hash_Table_Type (Count_Type'Max (New_Size, Next_Size),
                                         Container.Modulus);

      begin

         --  Make a perfect copy of Container.Content

         New_Set.Length := CC.Length;
         New_Set.Free   := CC.Free;

         --  Copy the node of Container

         for J in 1 .. CC.Capacity loop
            declare
               New_Node : Node_Type renames New_Set.Nodes (J);
               Old_Node : Node_Type renames CC.Nodes (J);

            begin
               Move (New_Node.E_Holder, Old_Node.E_Holder);
               New_Node.Next             := Old_Node.Next;
               New_Node.Has_Element      := Old_Node.Has_Element;
            end;
         end loop;

         --  Put the added node in the free list.
         --  It might be optimized by checking if New_Map.Free < 0 and,
         --  then just do nothing but it would make the unit relies on the
         --  current implementation of the hashed table. A change in the
         --  hashed table could thus create a sneaky bug here.

         for J in CC.Capacity + 1 .. New_Set.Capacity loop
            New_Set.Nodes (J).Has_Element := False;
            HT_Ops.Free (New_Set.all, J);
         end loop;

         --  Copy the buckets

         New_Set.Buckets (1 .. Container.Modulus) :=
           CC.Buckets (1 .. Container.Modulus);

         --  The table must be manually deallocated because it is not
         --  Controlled. Only Container (and the holder) are controlled
         --  here. This will not cause leaks since the ownership of the
         --  elements has been moved to New_Map.

         Finalize (Container);
         CC := New_Set;
      end;
   end Resize;

   ------------------
   --  Set_Element --
   ------------------

   procedure Set_Element (Node : in out Node_Type; Item : Element_Type) is
   begin
      Replace_Element (Node.E_Holder, Item);
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
            Delete (Target, Element (N.E_Holder));
         else
            Insert (Target, Element (N.E_Holder), Unused_X, B);
            pragma Assert (B);
         end if;
      end Process;

   --  Start of processing for Symmetric_Difference

   begin
      if Length (Target) = 0 then
         Assign (Target, Source);
         return;
      end if;

      Iterate (Source.Content.all);
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
         H : constant Hash_Type :=
           Default_Modulus (Length (Left) + Length (Right));

      begin
         return S : Set (H) do
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
      return S : Set (Modulus => 1) do
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
         E : constant Element_Type := Element (N.E_Holder);

         Unused_X : Count_Type;
         Unused_B : Boolean;

      begin
         Insert (Target, E, Unused_X, Unused_B);
      end Process;

   --  Start of processing for Union

   begin
      Iterate (Source.Content.all);
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
         H : constant Hash_Type :=
           Default_Modulus (Length (Left) + Length (Right));

      begin
         return S : Set (H) do
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
      if Position.Node = 0 then
         return True;
      end if;

      if Is_Empty (Container) then
         return False;
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
           (Element_Keys.Index
              (S.Content.all, Element (N (Position.Node).E_Holder)));

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

end SPARK.Containers.Formal.Unbounded_Hashed_Sets;
