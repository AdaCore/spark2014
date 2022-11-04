------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--              SPARK.CONTAINERS.FORMAL.UNBOUNDED_ORDERED_MAPS              --
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
with Ada.Containers.Red_Black_Trees.Generic_Bounded_Operations;
pragma Elaborate_All
  (Ada.Containers.Red_Black_Trees.Generic_Bounded_Operations);

with Ada.Containers.Red_Black_Trees.Generic_Bounded_Keys;
pragma Elaborate_All (Ada.Containers.Red_Black_Trees.Generic_Bounded_Keys);

with SPARK.Big_Integers;
use SPARK.Big_Integers;

with Ada.Unchecked_Deallocation;

with System; use type System.Address;

package body SPARK.Containers.Formal.Unbounded_Ordered_Maps with
  SPARK_Mode => Off
is

   --  Convert Count_Type to Big_Interger

   package Conversions is new Signed_Conversions (Int => Count_Type);

   function Big (J : Count_Type) return Big_Integer renames
     Conversions.To_Big_Integer;

   -----------------------------
   -- Node Access Subprograms --
   -----------------------------

   --  These subprograms provide a functional interface to access fields
   --  of a node, and a procedural interface for modifying these values.

   function Color
     (Node : Node_Type) return Ada.Containers.Red_Black_Trees.Color_Type;
   pragma Inline (Color);

   function Left_Son (Node : Node_Type) return Count_Type;
   pragma Inline (Left_Son);

   function Parent (Node : Node_Type) return Count_Type;
   pragma Inline (Parent);

   function Right_Son (Node : Node_Type) return Count_Type;
   pragma Inline (Right_Son);

   procedure Set_Color
     (Node  : in out Node_Type;
      Color : Ada.Containers.Red_Black_Trees.Color_Type);
   pragma Inline (Set_Color);

   procedure Set_Left (Node : in out Node_Type; Left : Count_Type);
   pragma Inline (Set_Left);

   procedure Set_Right (Node : in out Node_Type; Right : Count_Type);
   pragma Inline (Set_Right);

   procedure Set_Parent (Node : in out Node_Type; Parent : Count_Type);
   pragma Inline (Set_Parent);

   -----------------------
   -- Local Subprograms --
   -----------------------

   generic
      with procedure Set_Element (Node : in out Node_Type);
   procedure Generic_Allocate
     (Tree : in out Tree_Types.Tree_Type'Class;
      Node : out Count_Type);
   --  Get a Node out of the free list and output it. It also set its Element
   --  and Key using Set_Element.

   procedure Free (Tree : in out Map; X : Count_Type);
   --  Turn the Node X back to the free list and Finalize it

   function Is_Greater_Key_Node
     (Left  : Key_Type;
      Right : Node_Type) return Boolean;
   --  Check if the Key_Type Left is greater than the Key_Type held by Right

   pragma Inline (Is_Greater_Key_Node);

   function Is_Less_Key_Node
     (Left  : Key_Type;
      Right : Node_Type) return Boolean;
   --  Check if the Key_Type Left is smaller than the Key_Type held by Right

   pragma Inline (Is_Less_Key_Node);

   procedure Resize (Container : in out Map; Size : Count_Type := 0) with
   --  Allocate a new larger Tree

     Global => null,
     Post   => Model (Container) = Model (Container)'Old
                 and Positions (Container) = Positions (Container)'Old
                 and Keys (Container) = Keys (Container)'Old;

   --------------------------
   -- Local Instantiations --
   --------------------------

   procedure Finalize_Content is new Ada.Unchecked_Deallocation
     (Object => Tree_Types.Tree_Type,
      Name   => Tree_Access);
   --  Deallocate a Tree

   package Tree_Operations is
     new Red_Black_Trees.Generic_Bounded_Operations
       (Tree_Types => Tree_Types,
        Left       => Left_Son,
        Right      => Right_Son);

   use Tree_Operations;

   package Key_Ops is
     new Red_Black_Trees.Generic_Bounded_Keys
       (Tree_Operations     => Tree_Operations,
        Key_Type            => Key_Type,
        Is_Less_Key_Node    => Is_Less_Key_Node,
        Is_Greater_Key_Node => Is_Greater_Key_Node);

   ---------
   -- "=" --
   ---------

   function "=" (Left, Right : Map) return Boolean is
      Lst   : Count_Type;
      Node  : Count_Type;
      ENode : Count_Type;

   begin
      if Length (Left) /= Length (Right) then
         return False;
      end if;

      if Is_Empty (Left) then
         return True;
      end if;

      --  Loop over Left to check whether all the elements of Left are in Right
      --  or not.

      Lst := Next (Left.Content.all, Last (Left).Node);

      Node := First (Left).Node;
      while Node /= Lst loop
         ENode :=
           Find (Right, KHT.Element (Left.Content.Nodes (Node).K_Holder)).Node;

         if ENode = 0 or else
           EHT.Element (Left.Content.Nodes (Node).E_Holder) /=
           EHT.Element (Right.Content.Nodes (ENode).E_Holder)
         then
            return False;
         end if;

         Node := Next (Left.Content.all, Node);
      end loop;

      return True;
   end "=";

   ------------
   -- Adjust --
   ------------

   procedure Adjust (Container : in out Map) is
   begin
      if Container.Content = Empty_Tree'Access then
         return;
      end if;

      --  Make a perfect copy of the content

      declare
         New_Map : constant Tree_Access :=
           new Tree_Types.Tree_Type (Container.Content.Capacity);

      begin
         New_Map.First  := Container.Content.First;
         New_Map.Last   := Container.Content.Last;
         New_Map.Root   := Container.Content.Root;
         New_Map.Length := Container.Content.Length;
         New_Map.Free   := Container.Content.Free;

         New_Map.Nodes := Container.Content.Nodes;
         --  The call to Adjust on the holders will ensure a proper copy of
         --  the elements.

         --  The free list has been handle while copying the nodes

         Container.Content := New_Map;
      end;
   end Adjust;

   ------------
   -- Assign --
   ------------

   procedure Assign (Target : in out Map; Source : Map) is
      procedure Append_Element (Source_Node : Count_Type);

      procedure Append_Elements is
         new Tree_Operations.Generic_Iteration (Append_Element);

      --------------------
      -- Append_Element --
      --------------------

      procedure Append_Element (Source_Node : Count_Type) is
         SN : Node_Type renames Source.Content.Nodes (Source_Node);

         procedure Set_Element (Node : in out Node_Type);
         pragma Inline (Set_Element);

         function New_Node return Count_Type;
         pragma Inline (New_Node);

         procedure Insert_Post is new Key_Ops.Generic_Insert_Post (New_Node);

         procedure Unconditional_Insert_Sans_Hint is
           new Key_Ops.Generic_Unconditional_Insert (Insert_Post);

         procedure Unconditional_Insert_Avec_Hint is
           new Key_Ops.Generic_Unconditional_Insert_With_Hint
             (Insert_Post,
              Unconditional_Insert_Sans_Hint);

         procedure Allocate is new Generic_Allocate (Set_Element);

         --------------
         -- New_Node --
         --------------

         function New_Node return Count_Type is
            Result : Count_Type;
         begin
            Allocate (Target.Content.all, Result);
            return Result;
         end New_Node;

         -----------------
         -- Set_Element --
         -----------------

         procedure Set_Element (Node : in out Node_Type) is
         begin
            Node.K_Holder := SN.K_Holder;
            Node.E_Holder := SN.E_Holder;
         end Set_Element;

         Target_Node : Count_Type;

      --  Start of processing for Append_Element

      begin
         Unconditional_Insert_Avec_Hint
           (Tree  => Target.Content.all,
            Hint  => 0,
            Key   => KHT.Element (SN.K_Holder),
            Node  => Target_Node);
      end Append_Element;

   --  Start of processing for Assign

   begin
      if Target'Address = Source'Address then
         return;
      end if;

      --  Make sure there is enough room for all the elements of source in
      --  Target.

      if Target.Content.Capacity < Length (Source) then
         Resize (Target, Length (Source));
      end if;

      Tree_Operations.Clear_Tree (Target.Content.all);
      Append_Elements (Source.Content.all);
   end Assign;

   -------------
   -- Ceiling --
   -------------

   function Ceiling (Container : Map; Key : Key_Type) return Cursor is
      Node : constant Count_Type :=
        Key_Ops.Ceiling (Container.Content.all, Key);

   begin
      if Node = 0 then
         return No_Element;
      end if;

      return (Node => Node);
   end Ceiling;

   -----------
   -- Clear --
   -----------

   procedure Clear (Container : in out Map) is
   begin
      Tree_Operations.Clear_Tree (Container.Content.all);
   end Clear;

   -----------
   -- Color --
   -----------

   function Color (Node : Node_Type) return Color_Type is
   begin
      return Node.Color;
   end Color;

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

      pragma Assert (Vet (Container.Content.all, Position.Node),
                     "bad cursor in function Constant_Reference");

      return EHT.Element_Access
               (Container.Content.Nodes (Position.Node).E_Holder);
   end Constant_Reference;

   function Constant_Reference
     (Container : Map;
      Key       : Key_Type) return not null access constant Element_Type
   is
      Node : constant Node_Access := Find (Container, Key).Node;

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

   function Copy (Source : Map) return Map is
      Target : Map;

   begin
      if Source.Content = Empty_Tree'Access then
         return Target;
      end if;

      --  The implicit call to Adjust will properly copy the element

      Target.Content := new Tree_Types.Tree_Type'(Source.Content.all);

      return Target;
   end Copy;

   ------------
   -- Delete --
   ------------

   procedure Delete (Container : in out Map; Position : in out Cursor) is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with
           "Position cursor of Delete has no element";
      end if;

      pragma Assert (Vet (Container.Content.all, Position.Node),
                     "Position cursor of Delete is bad");

      Tree_Operations.Delete_Node_Sans_Free (Container.Content.all,
                                             Position.Node);
      Free (Container, Position.Node);
      Position := No_Element;
   end Delete;

   procedure Delete (Container : in out Map; Key : Key_Type) is
      X : constant Node_Access := Key_Ops.Find (Container.Content.all, Key);

   begin
      if X = 0 then
         raise Constraint_Error with "key not in map";
      end if;

      Tree_Operations.Delete_Node_Sans_Free (Container.Content.all, X);
      Free (Container, X);
   end Delete;

   ------------------
   -- Delete_First --
   ------------------

   procedure Delete_First (Container : in out Map) is
      X : constant Node_Access := First (Container).Node;
   begin
      if X /= 0 then
         Tree_Operations.Delete_Node_Sans_Free (Container.Content.all, X);
         Free (Container, X);
      end if;
   end Delete_First;

   -----------------
   -- Delete_Last --
   -----------------

   procedure Delete_Last (Container : in out Map) is
      X : constant Node_Access := Last (Container).Node;
   begin
      if X /= 0 then
         Tree_Operations.Delete_Node_Sans_Free (Container.Content.all, X);
         Free (Container, X);
      end if;
   end Delete_Last;

   -------------
   -- Element --
   -------------

   function Element (Container : Map; Position : Cursor) return Element_Type is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with
           "Position cursor of function Element has no element";
      end if;

      pragma Assert (Vet (Container.Content.all, Position.Node),
                     "Position cursor of function Element is bad");

      return EHT.Element (Container.Content.Nodes (Position.Node).E_Holder);

   end Element;

   function Element (Container : Map; Key : Key_Type) return Element_Type is
      Node : constant Node_Access := Find (Container, Key).Node;

   begin
      if Node = 0 then
         raise Constraint_Error with "key not in map";
      end if;

      return EHT.Element (Container.Content.Nodes (Node).E_Holder);
   end Element;

   ---------------------
   -- Equivalent_Keys --
   ---------------------

   function Equivalent_Keys (Left, Right : Key_Type) return Boolean is
   begin
      if Left < Right
        or else Right < Left
      then
         return False;
      else
         return True;
      end if;
   end Equivalent_Keys;

   -------------
   -- Exclude --
   -------------

   procedure Exclude (Container : in out Map; Key : Key_Type) is
      X : constant Node_Access := Key_Ops.Find (Container.Content.all, Key);
   begin
      if X /= 0 then
         Tree_Operations.Delete_Node_Sans_Free (Container.Content.all, X);
         Free (Container, X);
      end if;
   end Exclude;

   --------------
   -- Finalize --
   --------------

   procedure Finalize (Container : in out Map) is
   begin
      if Container.Content /= Empty_Tree'Access then
         declare
            Tree : Tree_Access := Container.Content;
         begin
            Container.Content := Empty_Tree'Access;
            Finalize_Content (Tree);
            --  The elements are in Controlled Holder_Type and thus will be
            --  deallocated properly.

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
   begin
      if Length (Container) = 0 then
         return No_Element;
      end if;

      return (Node => Container.Content.First);
   end First;

   -------------------
   -- First_Element --
   -------------------

   function First_Element (Container : Map) return Element_Type is
   begin
      if Is_Empty (Container) then
         raise Constraint_Error with "map is empty";
      end if;

      return EHT.Element
               (Container.Content.Nodes (First (Container).Node).E_Holder);
   end First_Element;

   ---------------
   -- First_Key --
   ---------------

   function First_Key (Container : Map) return Key_Type is
   begin
      if Is_Empty (Container) then
         raise Constraint_Error with "map is empty";
      end if;

      return KHT.Element
               (Container.Content.Nodes (First (Container).Node).K_Holder);
   end First_Key;

   -----------
   -- Floor --
   -----------

   function Floor (Container : Map; Key : Key_Type) return Cursor is
      Node : constant Count_Type := Key_Ops.Floor (Container.Content.all, Key);

   begin
      if Node = 0 then
         return No_Element;
      end if;

      return (Node => Node);
   end Floor;

   ------------------
   -- Formal_Model --
   ------------------

   package body Formal_Model is

      -------------------------
      -- Element_Logic_Equal --
      -------------------------

      function Element_Logic_Equal (Left, Right : Element_Type) return Boolean
      is
      begin
         Check_Or_Fail;
         return Left = Right;
      end Element_Logic_Equal;

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
            elsif Key < K.Get (Container, I) then
               return 0;
            end if;
         end loop;
         return 0;
      end Find;

      -------------------------
      -- K_Bigger_Than_Range --
      -------------------------

      function K_Bigger_Than_Range
        (Container : K.Sequence;
         Fst       : Positive_Count_Type;
         Lst       : Count_Type;
         Key       : Key_Type) return Boolean
      is
      begin
         for I in Fst .. Lst loop
            if not (K.Get (Container, I) < Key) then
               return False;
            end if;
         end loop;
         return True;
      end K_Bigger_Than_Range;

      ---------------
      -- K_Is_Find --
      ---------------

      function K_Is_Find
        (Container : K.Sequence;
         Key       : Key_Type;
         Position  : Count_Type) return Boolean
      is
      begin
         for I in 1 .. Position - 1 loop
            if Key < K.Get (Container, I) then
               return False;
            end if;
         end loop;

         if Position < K.Length (Container) then
            for I in Position + 1 .. K.Length (Container) loop
               if K.Get (Container, I) < Key then
                  return False;
               end if;
            end loop;
         end if;
         return True;
      end K_Is_Find;

      --------------------------
      -- K_Smaller_Than_Range --
      --------------------------

      function K_Smaller_Than_Range
        (Container : K.Sequence;
         Fst       : Positive_Count_Type;
         Lst       : Count_Type;
         Key       : Key_Type) return Boolean
      is
      begin
         for I in Fst .. Lst loop
            if not (Key < K.Get (Container, I)) then
               return False;
            end if;
         end loop;
         return True;
      end K_Smaller_Than_Range;

      ---------------------
      -- Key_Logic_Equal --
      ---------------------

      function Key_Logic_Equal (Left, Right : Key_Type) return Boolean is
      begin
         Check_Or_Fail;
         return Equivalent_Keys (Left, Right);
      end Key_Logic_Equal;

      ----------
      -- Keys --
      ----------

      function Keys (Container : Map) return K.Sequence is
         Position : Count_Type := Container.Content.First;
         R        : K.Sequence;

      begin
         --  Can't use First, Next or Element here, since they depend on models
         --  for their postconditions.

         while Position /= 0 loop
            R :=
              K.Add
                (R, KHT.Element (Container.Content.Nodes (Position).K_Holder));
            Position := Tree_Operations.Next (Container.Content.all, Position);
         end loop;

         return R;
      end Keys;

      ----------------------------
      -- Lift_Abstraction_Level --
      ----------------------------

      procedure Lift_Abstraction_Level (Container : Map) is null;

      -----------
      -- Model --
      -----------

      function Model (Container : Map) return M.Map is
         Position : Count_Type := Container.Content.First;
         R        : M.Map;

      begin
         --  Can't use First, Next or Element here, since they depend on models
         --  for their postconditions.

         while Position /= 0 loop
            R :=
              M.Add
                (Container => R,
                 New_Key   => KHT.Element
                                (Container.Content.Nodes (Position).K_Holder),
                 New_Item  => EHT.Element
                                (Container.Content.Nodes (Position).E_Holder));

            Position := Tree_Operations.Next (Container.Content.all, Position);
         end loop;

         return R;
      end Model;

      -------------------------
      -- P_Positions_Shifted --
      -------------------------

      function P_Positions_Shifted
        (Small : P.Map;
         Big   : P.Map;
         Cut   : Positive_Count_Type;
         Count : Count_Type := 1) return Boolean
      is
      begin
         for Cu of Small loop
            if not P.Has_Key (Big, Cu) then
               return False;
            end if;
         end loop;

         for Cu of Big loop
            declare
               Pos : constant Positive_Count_Type := P.Get (Big, Cu);

            begin
               if Pos < Cut then
                  if not P.Has_Key (Small, Cu)
                    or else Pos /= P.Get (Small, Cu)
                  then
                     return False;
                  end if;

               elsif Pos >= Cut + Count then
                  if not P.Has_Key (Small, Cu)
                    or else Pos /= P.Get (Small, Cu) + Count
                  then
                     return False;
                  end if;

               else
                  if P.Has_Key (Small, Cu) then
                     return False;
                  end if;
               end if;
            end;
         end loop;

         return True;
      end P_Positions_Shifted;

      ---------------
      -- Positions --
      ---------------

      function Positions (Container : Map) return P.Map is
         I        : Count_Type := 1;
         Position : Count_Type := Container.Content.First;
         R        : P.Map;

      begin
         --  Can't use First, Next or Element here, since they depend on models
         --  for their postconditions.

         while Position /= 0 loop
            R := P.Add (R, (Node => Position), I);
            pragma Assert (P.Length (R) = Big (I));
            Position := Tree_Operations.Next (Container.Content.all, Position);
            I := I + 1;
         end loop;

         return R;
      end Positions;

   end Formal_Model;

   ----------
   -- Free --
   ----------

   procedure Free
     (Tree : in out Map;
      X  : Count_Type)
   is
   begin

      --  It is not mandatory to Finalize the holder as there are controlled
      --  but this maintains the unused nodes empty.

      EHT.Finalize (Tree.Content.Nodes (X).E_Holder);
      KHT.Finalize (Tree.Content.Nodes (X).K_Holder);

      Tree.Content.Nodes (X).Has_Element := False;
      Tree_Operations.Free (Tree.Content.all, X);
   end Free;

   ----------------------
   -- Generic_Allocate --
   ----------------------

   procedure Generic_Allocate
     (Tree : in out Tree_Types.Tree_Type'Class;
      Node : out Count_Type)
   is
      procedure Allocate is
        new Tree_Operations.Generic_Allocate (Set_Element);
   begin
      Allocate (Tree, Node);
      Tree.Nodes (Node).Has_Element := True;
   end Generic_Allocate;

   -----------------
   -- Has_Element --
   -----------------

   function Has_Element (Container : Map; Position : Cursor) return Boolean is
   begin
      if Position.Node = 0
        or else Position.Node < 1
        or else Position.Node > Container.Content.Capacity
      then
         return False;
      end if;

      return Container.Content.Nodes (Position.Node).Has_Element;
   end Has_Element;

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
            N : Node_Type renames Container.Content.Nodes (Position.Node);
         begin
            KHT.Replace_Element (N.K_Holder, Key);
            EHT.Replace_Element (N.E_Holder, New_Item);
         end;
      end if;
   end Include;

   procedure Insert
     (Container : in out Map;
      Key       : Key_Type;
      New_Item  : Element_Type;
      Position  : out Cursor;
      Inserted  : out Boolean)
   is
      function New_Node return Node_Access;
      --  Allocate a new node and set is key to Key and is elment to New_Item.

      procedure Insert_Post is
        new Key_Ops.Generic_Insert_Post (New_Node);

      procedure Insert_Sans_Hint is
        new Key_Ops.Generic_Conditional_Insert (Insert_Post);

      --------------
      -- New_Node --
      --------------

      function New_Node return Node_Access is
         procedure Initialize (Node : in out Node_Type);
         procedure Allocate_Node is new Generic_Allocate (Initialize);

         procedure Initialize (Node : in out Node_Type) is
         begin
            KHT.Replace_Element (Node.K_Holder, Key);
            EHT.Replace_Element (Node.E_Holder, New_Item);
         end Initialize;

         X : Node_Access;

      begin
         Allocate_Node (Container.Content.all, X);
         return X;
      end New_Node;

   --  Start of processing for Insert

   begin

      --  Make sure there is enough room for the new element

      if Length (Container) = Container.Content.Capacity then
         Resize (Container);
      end if;

      Insert_Sans_Hint
        (Container.Content.all,
         Key,
         Position.Node,
         Inserted);
   end Insert;

   procedure Insert
     (Container : in out Map;
      Key       : Key_Type;
      New_Item  : Element_Type)
   is
      Position : Cursor;
      Inserted : Boolean;

   begin
      Insert (Container, Key, New_Item, Position, Inserted);

      if not Inserted then
         raise Constraint_Error with "key already in map";
      end if;
   end Insert;

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (Container : Map) return Boolean is
   begin
      return Length (Container) = 0;
   end Is_Empty;

   -------------------------
   -- Is_Greater_Key_Node --
   -------------------------

   function Is_Greater_Key_Node
     (Left  : Key_Type;
      Right : Node_Type) return Boolean
   is
   begin
      --  k > node same as node < k

      return KHT.Element (Right.K_Holder) < Left;
   end Is_Greater_Key_Node;

   ----------------------
   -- Is_Less_Key_Node --
   ----------------------

   function Is_Less_Key_Node
     (Left  : Key_Type;
      Right : Node_Type) return Boolean
   is
   begin
      return Left < KHT.Element (Right.K_Holder);
   end Is_Less_Key_Node;

   ---------
   -- Key --
   ---------

   function Key (Container : Map; Position : Cursor) return Key_Type is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with
           "Position cursor of function Key has no element";
      end if;

      pragma Assert (Vet (Container.Content.all, Position.Node),
                     "Position cursor of function Key is bad");

      return KHT.Element (Container.Content.Nodes (Position.Node).K_Holder);
   end Key;

   ----------
   -- Last --
   ----------

   function Last (Container : Map) return Cursor is
   begin
      if Length (Container) = 0 then
         return No_Element;
      end if;

      return (Node => Container.Content.Last);
   end Last;

   ------------------
   -- Last_Element --
   ------------------

   function Last_Element (Container : Map) return Element_Type is
   begin
      if Is_Empty (Container) then
         raise Constraint_Error with "map is empty";
      end if;

      return EHT.Element
        (Container.Content.Nodes (Last (Container).Node).E_Holder);
   end Last_Element;

   --------------
   -- Last_Key --
   --------------

   function Last_Key (Container : Map) return Key_Type is
   begin
      if Is_Empty (Container) then
         raise Constraint_Error with "map is empty";
      end if;

      return KHT.Element
               (Container.Content.Nodes (Last (Container).Node).K_Holder);
   end Last_Key;

   --------------
   -- Left_Son --
   --------------

   function Left_Son (Node : Node_Type) return Count_Type is
   begin
      return Node.Left;
   end Left_Son;

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
      if Target'Address = Source'Address then
         return;
      end if;

      Finalize (Target);

      Target.Content := Source.Content;
      Source.Content := Empty_Tree'Access;
   end Move;

   ----------
   -- Next --
   ----------

   procedure Next (Container : Map; Position : in out Cursor) is
   begin
      Position := Next (Container, Position);
   end Next;

   function Next (Container : Map; Position : Cursor) return Cursor is
   begin
      if Position = No_Element then
         return No_Element;
      end if;

      if not Has_Element (Container, Position) then
         raise Constraint_Error;
      end if;

      pragma Assert (Vet (Container.Content.all, Position.Node),
                     "bad cursor in Next");

      return (Node => Tree_Operations.Next
                        (Container.Content.all, Position.Node));
   end Next;

   ------------
   -- Parent --
   ------------

   function Parent (Node : Node_Type) return Count_Type is
   begin
      return Node.Parent;
   end Parent;

   --------------
   -- Previous --
   --------------

   procedure Previous (Container : Map; Position : in out Cursor) is
   begin
      Position := Previous (Container, Position);
   end Previous;

   function Previous (Container : Map; Position : Cursor) return Cursor is
   begin
      if Position = No_Element then
         return No_Element;
      end if;

      if not Has_Element (Container, Position) then
         raise Constraint_Error;
      end if;

      pragma Assert (Vet (Container.Content.all, Position.Node),
                     "bad cursor in Previous");

      declare
         Node : constant Count_Type :=
           Tree_Operations.Previous (Container.Content.all, Position.Node);

      begin
         if Node = 0 then
            return No_Element;
         end if;

         return (Node => Node);
      end;
   end Previous;

   --------------
   -- Reference --
   --------------

   function Reference
     (Container : not null access Map;
      Position  : Cursor) return not null access Element_Type
   is
   begin
      if not Has_Element (Container.all, Position) then
         raise Constraint_Error with "Position cursor has no element";
      end if;

      pragma Assert
        (Vet (Container.Content.all, Position.Node),
         "bad cursor in function Reference");

      return EHT.Element_Access
               (Container.Content.Nodes (Position.Node).E_Holder);
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
      Node : constant Node_Access :=
        Key_Ops.Find (Container.Content.all, Key);
   begin
      if Node = 0 then
         raise Constraint_Error with "key not in map";
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

      pragma Assert (Vet (Container.Content.all, Position.Node),
                     "Position cursor of Replace_Element is bad");

      EHT.Replace_Element
        (Container.Content.Nodes (Position.Node).E_Holder, New_Item);
   end Replace_Element;

   ------------
   -- Resize --
   ------------

   procedure Resize (Container : in out Map; Size : Count_Type := 0) is
      Min_Size : constant Count_Type := 100;
      New_Size : constant Count_Type := Count_Type'Max (Min_Size, Size);

      CC : Tree_Access renames Container.Content;

   begin
      if CC = Empty_Tree'Access then
         CC := new Tree_Types.Tree_Type (New_Size);
         return;
      end if;

      if CC.Nodes'Length = Count_Type'Last then
         raise Constraint_Error with "Ordered Map already at size max";
      end if;

      if Size /= 0 and then CC.Capacity >= Size then
         return;
      end if;

      declare
         Next_Size : constant Count_Type :=
           (if CC.Nodes'Length < Count_Type'Last / 2
            then 2 * CC.Nodes'Length
            else Count_Type'Last);
         New_Map : constant Tree_Access :=
           new Tree_Types.Tree_Type (Count_Type'Max (New_Size, Next_Size));

      begin

         --  Make a perfect copy of Container.Content

         New_Map.First  := CC.First;
         New_Map.Last   := CC.Last;
         New_Map.Root   := CC.Root;
         New_Map.Length := CC.Length;
         New_Map.Free   := CC.Free;

         --  Copy the nodes. It is not possible to use an affectation
         --  because it wouild copy the element instead of moving them.

         for J in 1 .. CC.Capacity loop
            declare
               New_Node : Node_Type renames New_Map.Nodes (J);
               Old_Node : Node_Type renames CC.Nodes (J);

            begin
               New_Node.Has_Element := Old_Node.Has_Element;
               New_Node.Parent      := Old_Node.Parent;
               New_Node.Left        := Old_Node.Left;
               New_Node.Right       := Old_Node.Right;
               New_Node.Color       := Old_Node.Color;
               KHT.Move (New_Node.K_Holder, Old_Node.K_Holder);
               EHT.Move (New_Node.E_Holder, Old_Node.E_Holder);
            end;
         end loop;

         --  Put the added node in the free list.
         --  It might be optimized by checking if New_Map.Free < 0 and,
         --  then just do nothing but it would make the unit relies on the
         --  current implementation of the Red Black Trees. A change in the
         --  Red Black Trees could thus create a sneaky bug here.

         for J in CC.Capacity + 1 .. New_Map.Capacity loop
            New_Map.Nodes (J).Has_Element := False;
            Tree_Operations.Free (New_Map.all, J);
         end loop;

         Finalize (Container);
         CC := New_Map;
      end;
   end Resize;

   ---------------
   -- Right_Son --
   ---------------

   function Right_Son (Node : Node_Type) return Count_Type is
   begin
      return Node.Right;
   end Right_Son;

   ---------------
   -- Set_Color --
   ---------------

   procedure Set_Color (Node  : in out Node_Type; Color : Color_Type) is
   begin
      Node.Color := Color;
   end Set_Color;

   --------------
   -- Set_Left --
   --------------

   procedure Set_Left (Node : in out Node_Type; Left : Count_Type) is
   begin
      Node.Left := Left;
   end Set_Left;

   ----------------
   -- Set_Parent --
   ----------------

   procedure Set_Parent (Node : in out Node_Type; Parent : Count_Type) is
   begin
      Node.Parent := Parent;
   end Set_Parent;

   ---------------
   -- Set_Right --
   ---------------

   procedure Set_Right (Node : in out Node_Type; Right : Count_Type) is
   begin
      Node.Right := Right;
   end Set_Right;

end SPARK.Containers.Formal.Unbounded_Ordered_Maps;
