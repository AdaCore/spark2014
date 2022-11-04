------------------------------------------------------------------------------
--                                                                          --
--                        SPARK LIBRARY COMPONENTS                          --
--                                                                          --
--              SPARK.CONTAINERS.FORMAL.UNBOUNDED_ORDERED_SETS              --
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

with Ada.Containers.Red_Black_Trees.Generic_Bounded_Set_Operations;
pragma Elaborate_All
  (Ada.Containers.Red_Black_Trees.Generic_Bounded_Set_Operations);

with System; use type System.Address;

with Ada.Unchecked_Deallocation;

package body SPARK.Containers.Formal.Unbounded_Ordered_Sets with
  SPARK_Mode => Off
is

   ------------------------------
   -- Access to Fields of Node --
   ------------------------------

   --  These subprograms provide functional notation for access to fields
   --  of a node, and procedural notation for modifiying these fields.

   function Color (Node : Node_Type) return Red_Black_Trees.Color_Type;
   pragma Inline (Color);

   function Left_Son (Node : Node_Type) return Count_Type;
   pragma Inline (Left_Son);

   function Parent (Node : Node_Type) return Count_Type;
   pragma Inline (Parent);

   function Right_Son (Node : Node_Type) return Count_Type;
   pragma Inline (Right_Son);

   procedure Set_Color
     (Node  : in out Node_Type;
      Color : Red_Black_Trees.Color_Type);
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

   procedure Assign
     (Target : in out Tree_Types.Tree_Type;
      Source : Tree_Types.Tree_Type);
   --  Clear Target add insert all the element of source in it

   generic
      with procedure Set_Element (Node : in out Node_Type);
   procedure Generic_Allocate
     (Tree : in out Tree_Types.Tree_Type'Class;
      Node : out Count_Type);
   --  Allocate a new Node (get it out of he free list) and set its element
   --  using Set_Element.

   procedure Free (Tree : in out Set; X : Count_Type);
   --  Finalize the Holder_Type in the Node_Type pointed by X and turn back the
   --  Node_Type to the free list.

   procedure Insert_Sans_Hint
     (Container : in out Tree_Types.Tree_Type;
      New_Item  : Element_Type;
      Node      : out Count_Type;
      Inserted  : out Boolean);
   --  Insert New_Item in Container. Node refer to the inserted Node_Type.
   --  The flag Inserted is set to false if New_Item was not copied in Node.
   --  This might happen, for exemple, if it was already in the tree.

   procedure Insert_With_Hint
     (Dst_Set  : in out Tree_Types.Tree_Type;
      Dst_Hint : Count_Type;
      Src_Node : Node_Type;
      Dst_Node : out Count_Type);
   --  Insert the Src_Node Node_Type in the tree by copying its element in
   --  Dst_Node. The Dst_Hint help the insertion if it refer to a neighbour
   --  of the correct position fo Src_Node.

   function Is_Greater_Element_Node
     (Left  : Element_Type;
      Right : Node_Type) return Boolean;
   pragma Inline (Is_Greater_Element_Node);
   --  Comparison function for tree's operations

   function Is_Less_Element_Node
     (Left  : Element_Type;
      Right : Node_Type) return Boolean;
   pragma Inline (Is_Less_Element_Node);
   --  Comparison function for tree's operations

   function Is_Less_Node_Node (L, R : Node_Type) return Boolean;
   pragma Inline (Is_Less_Node_Node);
   --  Comparison function for tree's operations

   procedure Replace_Element
     (Tree : in out Set;
      Node : Count_Type;
      Item : Element_Type);
   --  Delete the Node_Type Node and insert Item in Tree

   procedure Resize (Container : in out Set; Size : Count_Type := 0) with
   --  Allocate a new larger Tree

     Global => null,
     Post   => Model (Container) = Model (Container)'Old
                 and Elements (Container) = Elements (Container)'Old
                 and Positions (Container) = Positions (Container)'Old;

   procedure Finalize_Content is new Ada.Unchecked_Deallocation
     (Object => Tree_Types.Tree_Type,
      Name   => Tree_Access);

   --------------------------
   -- Local Instantiations --
   --------------------------

   package Tree_Operations is
     new Red_Black_Trees.Generic_Bounded_Operations
       (Tree_Types,
        Left  => Left_Son,
        Right => Right_Son);

   use Tree_Operations;

   package Element_Keys is
     new Red_Black_Trees.Generic_Bounded_Keys
       (Tree_Operations     => Tree_Operations,
        Key_Type            => Element_Type,
        Is_Less_Key_Node    => Is_Less_Element_Node,
        Is_Greater_Key_Node => Is_Greater_Element_Node);

   package Set_Ops is
     new Red_Black_Trees.Generic_Bounded_Set_Operations
       (Tree_Operations  => Tree_Operations,
        Set_Type         => Tree_Types.Tree_Type,
        Assign           => Assign,
        Insert_With_Hint => Insert_With_Hint,
        Is_Less          => Is_Less_Node_Node);

   ---------
   -- "=" --
   ---------

   function "=" (Left, Right : Set) return Boolean is
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

      Lst := Next (Left.Content.all, Last (Left).Node);

      Node := First (Left).Node;
      while Node /= Lst loop
         ENode := Find
           (Right, Element (Left.Content.Nodes (Node).E_Holder)).Node;
         if ENode = 0
           or else Element (Left.Content.Nodes (Node).E_Holder) /=
           Element (Right.Content.Nodes (ENode).E_Holder)
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

   procedure Adjust (S : in out Set) is
      Tree : Tree_Access;
   begin
      if S.Content = Empty_Tree'Access then
         return;
      end if;

      Tree := new Tree_Types.Tree_Type'(S.Content.all);

      S.Content := Tree;
   end Adjust;

   ------------
   -- Assign --
   ------------

   procedure Assign
     (Target : in out Tree_Types.Tree_Type;
      Source : Tree_Types.Tree_Type)
   is
      procedure Append_Element (Source_Node : Count_Type);

      procedure Append_Elements is
        new Tree_Operations.Generic_Iteration (Append_Element);

      --------------------
      -- Append_Element --
      --------------------

      procedure Append_Element (Source_Node : Count_Type) is
         SN : Node_Type renames Source.Nodes (Source_Node);

         procedure Set_Element (Node : in out Node_Type);
         pragma Inline (Set_Element);

         function New_Node return Count_Type;
         pragma Inline (New_Node);

         procedure Insert_Post is
           new Element_Keys.Generic_Insert_Post (New_Node);

         procedure Unconditional_Insert_Sans_Hint is
           new Element_Keys.Generic_Unconditional_Insert (Insert_Post);

         procedure Unconditional_Insert_Avec_Hint is
           new Element_Keys.Generic_Unconditional_Insert_With_Hint
                 (Insert_Post,
                  Unconditional_Insert_Sans_Hint);

         procedure Allocate is new Generic_Allocate (Set_Element);

         --------------
         -- New_Node --
         --------------

         function New_Node return Count_Type is
            Result : Count_Type;
         begin
            Allocate (Target, Result);
            return Result;
         end New_Node;

         -----------------
         -- Set_Element --
         -----------------

         procedure Set_Element (Node : in out Node_Type) is
         begin
            Node.E_Holder := SN.E_Holder;
         end Set_Element;

         --  Local variables

         Target_Node : Count_Type;

      --  Start of processing for Append_Element

      begin
         Unconditional_Insert_Avec_Hint
           (Tree  => Target,
            Hint  => 0,
            Key   => Element (SN.E_Holder),
            Node  => Target_Node);
      end Append_Element;

   --  Start of processing for Assign

   begin
      if Target'Address = Source'Address then
         return;
      end if;

      Tree_Operations.Clear_Tree (Target);
      Append_Elements (Source);
   end Assign;

   procedure Assign (Target : in out Set; Source : Set) is
   begin
      Clear (Target);

      if Target.Content.Capacity < Length (Source)
      then
         Resize (Target, Length (Source));
      end if;

      Assign (Target.Content.all, Source.Content.all);
   end Assign;

   -------------
   -- Ceiling --
   -------------

   function Ceiling (Container : Set; Item : Element_Type) return Cursor is
      Node : constant Count_Type :=
        Element_Keys.Ceiling (Container.Content.all, Item);

   begin
      if Node = 0 then
         return No_Element;
      end if;

      return (Node => Node);
   end Ceiling;

   -----------
   -- Clear --
   -----------

   procedure Clear (Container : in out Set) is
   begin
      Tree_Operations.Clear_Tree (Container.Content.all);
   end Clear;

   -----------
   -- Color --
   -----------

   function Color (Node : Node_Type) return Red_Black_Trees.Color_Type is
   begin
      return Node.Color;
   end Color;

   ------------------------
   -- Constant_Reference --
   ------------------------

   function Constant_Reference
     (Container : Set;
      Position  : Cursor) return not null access constant Element_Type
   is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with "Position cursor has no element";
      end if;

      pragma Assert (Vet (Container.Content.all, Position.Node),
                     "bad cursor in Element");

      return Element_Holder.Element_Access
               (Container.Content.Nodes (Position.Node).E_Holder);
   end Constant_Reference;

   --------------
   -- Contains --
   --------------

   function Contains
     (Container : Set;
      Item      : Element_Type) return Boolean
   is
   begin
      return Find (Container, Item) /= No_Element;
   end Contains;

   ----------
   -- Copy --
   ----------

   function Copy (Source : Set) return Set is
      Target : Set;

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

   procedure Delete (Container : in out Set; Position : in out Cursor) is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with "Position cursor has no element";
      end if;

      pragma Assert (Vet (Container.Content.all, Position.Node),
                     "bad cursor in Delete");

      Tree_Operations.Delete_Node_Sans_Free (Container.Content.all,
                                             Position.Node);
      Free (Container, Position.Node);
      Position := No_Element;
   end Delete;

   procedure Delete (Container : in out Set; Item : Element_Type) is
      X : constant Count_Type :=
        Element_Keys.Find (Container.Content.all, Item);

   begin
      if X = 0 then
         raise Constraint_Error with "attempt to delete element not in set";
      end if;

      Tree_Operations.Delete_Node_Sans_Free (Container.Content.all, X);
      Free (Container, X);
   end Delete;

   ------------------
   -- Delete_First --
   ------------------

   procedure Delete_First (Container : in out Set) is
      X : constant Count_Type := Container.Content.First;

   begin
      if X /= 0 then
         Tree_Operations.Delete_Node_Sans_Free (Container.Content.all, X);
         Free (Container, X);
      end if;
   end Delete_First;

   -----------------
   -- Delete_Last --
   -----------------

   procedure Delete_Last (Container : in out Set) is
      X : constant Count_Type := Container.Content.Last;

   begin
      if X /= 0 then
         Tree_Operations.Delete_Node_Sans_Free (Container.Content.all, X);
         Free (Container, X);
      end if;
   end Delete_Last;

   ----------------
   -- Difference --
   ----------------

   procedure Difference (Target : in out Set; Source : Set) is
   begin
      Set_Ops.Set_Difference (Target.Content.all, Source.Content.all);
   end Difference;

   function Difference (Left, Right : Set) return Set is
   begin
      if Left'Address = Right'Address then
         return Empty_Set;
      end if;

      if Length (Left) = 0 then
         return Empty_Set;
      end if;

      if Length (Right) = 0 then
         return Copy (Left);
      end if;

      return S : Set do
         S.Content := new Tree_Types.Tree_Type'
           (Set_Ops.Set_Difference (Left.Content.all, Right.Content.all));
      end return;
   end Difference;

   -------------
   -- Element --
   -------------

   function Element (Container : Set; Position : Cursor) return Element_Type is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with "Position cursor has no element";
      end if;

      pragma Assert (Vet (Container.Content.all, Position.Node),
                     "bad cursor in Element");

      return Element (Container.Content.Nodes (Position.Node).E_Holder);
   end Element;

   ---------------
   -- Empty_Set --
   ---------------

   function Empty_Set return Set is
     ((Ada.Finalization.Controlled with Content => Empty_Tree'Access));

   -------------------------
   -- Equivalent_Elements --
   -------------------------

   function Equivalent_Elements (Left, Right : Element_Type) return Boolean is
   begin
      if Left < Right
        or else Right < Left
      then
         return False;
      else
         return True;
      end if;
   end Equivalent_Elements;

   ---------------------
   -- Equivalent_Sets --
   ---------------------

   function Equivalent_Sets (Left, Right : Set) return Boolean is
      function Is_Equivalent_Node_Node
        (L, R : Node_Type) return Boolean;
      pragma Inline (Is_Equivalent_Node_Node);

      function Is_Equivalent is
        new Tree_Operations.Generic_Equal (Is_Equivalent_Node_Node);

      -----------------------------
      -- Is_Equivalent_Node_Node --
      -----------------------------

      function Is_Equivalent_Node_Node (L, R : Node_Type) return Boolean is
      begin
         if Element (L.E_Holder) < Element (R.E_Holder) then
            return False;
         elsif Element (R.E_Holder) < Element (L.E_Holder) then
            return False;
         else
            return True;
         end if;
      end Is_Equivalent_Node_Node;

   --  Start of processing for Equivalent_Sets

   begin
      return Is_Equivalent (Left.Content.all, Right.Content.all);
   end Equivalent_Sets;

   -------------
   -- Exclude --
   -------------

   procedure Exclude (Container : in out Set; Item : Element_Type) is
      X : constant Count_Type :=
        Element_Keys.Find (Container.Content.all, Item);

   begin
      if X /= 0 then
         Tree_Operations.Delete_Node_Sans_Free (Container.Content.all, X);
         Free (Container, X);
      end if;
   end Exclude;

   --------------
   -- Finalize --
   --------------

   procedure Finalize (S : in out Set) is
   begin
      if S.Content = Empty_Tree'Access then
         return;
      end if;

      declare
         Tree : Tree_Access := S.Content;
      begin
         S.Content := Empty_Tree'Access;
         Finalize_Content (Tree);
      end;
   end Finalize;

   ----------
   -- Find --
   ----------

   function Find (Container : Set; Item : Element_Type) return Cursor is
      Node : constant Count_Type :=
        Element_Keys.Find (Container.Content.all, Item);

   begin
      return (Node => Node);
   end Find;

   -----------
   -- First --
   -----------

   function First (Container : Set) return Cursor is
   begin
      return (Node => Container.Content.First);
   end First;

   -------------------
   -- First_Element --
   -------------------

   function First_Element (Container : Set) return Element_Type is
      Fst : constant Count_Type := First (Container).Node;
   begin
      if Fst = 0 then
         raise Constraint_Error with "set is empty";
      end if;

      declare
         N : Tree_Types.Nodes_Type renames Container.Content.Nodes;
      begin
         return Element (N (Fst).E_Holder);
      end;
   end First_Element;

   -----------
   -- Floor --
   -----------

   function Floor (Container : Set; Item : Element_Type) return Cursor is
      Node : constant Count_Type :=
        Element_Keys.Floor (Container.Content.all, Item);
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
      -- E_Bigger_Than_Range --
      -------------------------

      function E_Bigger_Than_Range
        (Container : E.Sequence;
         Fst       : Positive_Count_Type;
         Lst       : Count_Type;
         Item      : Element_Type) return Boolean
      is
      begin
         for I in Fst .. Lst loop
            if not (E.Get (Container, I) < Item) then
               return False;
            end if;
         end loop;

         return True;
      end E_Bigger_Than_Range;

      ----------------------
      -- E_Elements_Equal --
      ----------------------

      function E_Elements_Equal
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
      end E_Elements_Equal;

      -------------------------
      -- E_Elements_Included --
      -------------------------

      function E_Elements_Included
        (Left  : E.Sequence;
         Right : E.Sequence) return Boolean
      is
      begin
         for I in 1 .. E.Length (Left) loop
            declare
               J : constant Count_Type :=
                 E.Find (Right, E.Get (Left, I));
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
         for I in 1 .. E.Length (Left) loop
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
         for I in 1 .. E.Length (Container) loop
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

      ---------------
      -- E_Is_Find --
      ---------------

      function E_Is_Find
        (Container : E.Sequence;
         Item      : Element_Type;
         Position  : Count_Type) return Boolean
      is
      begin
         for I in 1 .. Position - 1 loop
            if Item < E.Get (Container, I) then
               return False;
            end if;
         end loop;

         if Position < E.Length (Container) then
            for I in Position + 1 .. E.Length (Container) loop
               if E.Get (Container, I) < Item then
                  return False;
               end if;
            end loop;
         end if;

         return True;
      end E_Is_Find;

      --------------------------
      -- E_Smaller_Than_Range --
      --------------------------

      function E_Smaller_Than_Range
        (Container : E.Sequence;
         Fst       : Positive_Count_Type;
         Lst       : Count_Type;
         Item      : Element_Type) return Boolean
      is
      begin
         for I in Fst .. Lst loop
            if not (Item < E.Get (Container, I)) then
               return False;
            end if;
         end loop;

         return True;
      end E_Smaller_Than_Range;

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
         Position : Count_Type := Container.Content.First;
         R        : E.Sequence;
      begin
         --  Can't use First, Next or Element here, since they depend on models
         --  for their postconditions.

         while Position /= 0 loop
            R := E.Add
              (R, Element (Container.Content.Nodes (Position).E_Holder));
            Position := Tree_Operations.Next (Container.Content.all, Position);
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
                    or else P.Get (P_Left,  C) > E.Length (E_Left)
                    or else P.Get (P_Right, C) > E.Length (E_Right)
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
         Position : Count_Type := Container.Content.First;
         R        : M.Set;

      begin
         --  Can't use First, Next or Element here, since they depend on models
         --  for their postconditions.

         while Position /= 0 loop
            R :=
              M.Add
                (Container => R,
                 Item      =>
                   Element (Container.Content.Nodes (Position).E_Holder));

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

      function Positions (Container : Set) return P.Map is
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

   procedure Free (Tree : in out Set; X : Count_Type) is
   begin
      Finalize (Tree.Content.Nodes (X).E_Holder);

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

   ------------------
   -- Generic_Keys --
   ------------------

   package body Generic_Keys with SPARK_Mode => Off is

      -----------------------
      -- Local Subprograms --
      -----------------------

      function Is_Greater_Key_Node
        (Left  : Key_Type;
         Right : Node_Type) return Boolean;
      pragma Inline (Is_Greater_Key_Node);

      function Is_Less_Key_Node
        (Left  : Key_Type;
         Right : Node_Type) return Boolean;
      pragma Inline (Is_Less_Key_Node);

      --------------------------
      -- Local Instantiations --
      --------------------------

      package Key_Keys is
        new Red_Black_Trees.Generic_Bounded_Keys
          (Tree_Operations     => Tree_Operations,
           Key_Type            => Key_Type,
           Is_Less_Key_Node    => Is_Less_Key_Node,
           Is_Greater_Key_Node => Is_Greater_Key_Node);

      -------------
      -- Ceiling --
      -------------

      function Ceiling (Container : Set; Key : Key_Type) return Cursor is
         Node : constant Count_Type :=
           Key_Keys.Ceiling (Container.Content.all, Key);

      begin
         if Node = 0 then
            return No_Element;
         end if;

         return (Node => Node);
      end Ceiling;

      --------------
      -- Contains --
      --------------

      function Contains (Container : Set; Key : Key_Type) return Boolean is
      begin
         return Find (Container, Key) /= No_Element;
      end Contains;

      ------------
      -- Delete --
      ------------

      procedure Delete (Container : in out Set; Key : Key_Type) is
         X : constant Count_Type := Key_Keys.Find (Container.Content.all, Key);

      begin
         if X = 0 then
            raise Constraint_Error with "attempt to delete key not in set";
         end if;

         Delete_Node_Sans_Free (Container.Content.all, X);
         Free (Container, X);
      end Delete;

      -------------
      -- Element --
      -------------

      function Element (Container : Set; Key : Key_Type) return Element_Type is
         Node : constant Count_Type :=
           Key_Keys.Find (Container.Content.all, Key);

      begin
         if Node = 0 then
            raise Constraint_Error with "key not in set";
         end if;

         declare
            N : Tree_Types.Nodes_Type renames Container.Content.Nodes;
         begin
            return Element (N (Node).E_Holder);
         end;
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

      procedure Exclude (Container : in out Set; Key : Key_Type) is
         X : constant Count_Type := Key_Keys.Find (Container.Content.all, Key);
      begin
         if X /= 0 then
            Delete_Node_Sans_Free (Container.Content.all, X);
            Free (Container, X);
         end if;
      end Exclude;

      ----------
      -- Find --
      ----------

      function Find (Container : Set; Key : Key_Type) return Cursor is
         Node : constant Count_Type :=
           Key_Keys.Find (Container.Content.all, Key);
      begin
         return (if Node = 0 then No_Element else (Node => Node));
      end Find;

      -----------
      -- Floor --
      -----------

      function Floor (Container : Set; Key : Key_Type) return Cursor is
         Node : constant Count_Type :=
           Key_Keys.Floor (Container.Content.all, Key);
      begin
         return (if Node = 0 then No_Element else (Node => Node));
      end Floor;

      ------------------
      -- Formal_Model --
      ------------------

      package body Formal_Model is

         -------------------------
         -- E_Bigger_Than_Range --
         -------------------------

         function E_Bigger_Than_Range
           (Container : E.Sequence;
            Fst       : Positive_Count_Type;
            Lst       : Count_Type;
            Key       : Key_Type) return Boolean
         is
         begin
            for I in Fst .. Lst loop
               if not (Generic_Keys.Key (E.Get (Container, I)) < Key) then
                  return False;
               end if;
            end loop;
            return True;
         end E_Bigger_Than_Range;

         ---------------
         -- E_Is_Find --
         ---------------

         function E_Is_Find
           (Container : E.Sequence;
            Key       : Key_Type;
            Position  : Count_Type) return Boolean
         is
         begin
            for I in 1 .. Position - 1 loop
               if Key < Generic_Keys.Key (E.Get (Container, I)) then
                  return False;
               end if;
            end loop;

            if Position < E.Length (Container) then
               for I in Position + 1 .. E.Length (Container) loop
                  if Generic_Keys.Key (E.Get (Container, I)) < Key then
                     return False;
                  end if;
               end loop;
            end if;
            return True;
         end E_Is_Find;

         --------------------------
         -- E_Smaller_Than_Range --
         --------------------------

         function E_Smaller_Than_Range
           (Container : E.Sequence;
            Fst       : Positive_Count_Type;
            Lst       : Count_Type;
            Key       : Key_Type) return Boolean
         is
         begin
            for I in Fst .. Lst loop
               if not (Key < Generic_Keys.Key (E.Get (Container, I))) then
                  return False;
               end if;
            end loop;
            return True;
         end E_Smaller_Than_Range;

         ----------
         -- Find --
         ----------

         function Find
           (Container : E.Sequence;
            Key       : Key_Type) return Count_Type
         is
         begin
            for I in 1 .. E.Length (Container) loop
               if Equivalent_Keys
                   (Key, Generic_Keys.Key (E.Get (Container, I)))
               then
                  return I;
               end if;
            end loop;
            return 0;
         end Find;

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

      -------------------------
      -- Is_Greater_Key_Node --
      -------------------------

      function Is_Greater_Key_Node
        (Left  : Key_Type;
         Right : Node_Type) return Boolean
      is
      begin
         return Key (Element (Right.E_Holder)) < Left;
      end Is_Greater_Key_Node;

      ----------------------
      -- Is_Less_Key_Node --
      ----------------------

      function Is_Less_Key_Node
        (Left  : Key_Type;
         Right : Node_Type) return Boolean
      is
      begin
         return Left < Key (Element (Right.E_Holder));
      end Is_Less_Key_Node;

      ---------
      -- Key --
      ---------

      function Key (Container : Set; Position : Cursor) return Key_Type is
      begin
         if not Has_Element (Container, Position) then
            raise Constraint_Error with
              "Position cursor has no element";
         end if;

         pragma Assert (Vet (Container.Content.all, Position.Node),
                        "bad cursor in Key");

         declare
            N : Tree_Types.Nodes_Type renames Container.Content.Nodes;
         begin
            return Key (Element (N (Position.Node).E_Holder));
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
         Node : constant Count_Type := Key_Keys.Find
           (Container.Content.all, Key);
      begin
         if not Has_Element (Container, (Node => Node)) then
            raise Constraint_Error with "attempt to replace key not in set";
         else
            Replace_Element (Container, Node, New_Item);
         end if;
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
      then
         return False;
      else
         return Container.Content.Nodes (Position.Node).Has_Element;
      end if;
   end Has_Element;

   -------------
   -- Include --
   -------------

   procedure Include (Container : in out Set; New_Item : Element_Type) is
      Position : Cursor;
      Inserted : Boolean;

   begin
      Insert (Container, New_Item, Position, Inserted);

      if not Inserted then
         declare
            N : Tree_Types.Nodes_Type renames Container.Content.Nodes;
         begin
            Replace_Element (N (Position.Node).E_Holder, New_Item);
         end;
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

      if Length (Container) >= Container.Content.Nodes'Length then
         Resize (Container);
      end if;
      Insert_Sans_Hint
        (Container.Content.all, New_Item, Position.Node, Inserted);
   end Insert;

   procedure Insert
     (Container : in out Set;
      New_Item  : Element_Type)
   is
      Position : Cursor;
      Inserted : Boolean;

   begin
      Insert (Container, New_Item, Position, Inserted);

      if not Inserted then
         raise Constraint_Error with
           "attempt to insert element already in set";
      end if;
   end Insert;

   ----------------------
   -- Insert_Sans_Hint --
   ----------------------

   procedure Insert_Sans_Hint
     (Container : in out Tree_Types.Tree_Type;
      New_Item  : Element_Type;
      Node      : out Count_Type;
      Inserted  : out Boolean)
   is
      procedure Set_Element (Node : in out Node_Type);

      function New_Node return Count_Type;
      pragma Inline (New_Node);

      procedure Insert_Post is
        new Element_Keys.Generic_Insert_Post (New_Node);

      procedure Conditional_Insert_Sans_Hint is
        new Element_Keys.Generic_Conditional_Insert (Insert_Post);

      procedure Allocate is new Generic_Allocate (Set_Element);

      --------------
      -- New_Node --
      --------------

      function New_Node return Count_Type is
         Result : Count_Type;
      begin
         Allocate (Container, Result);
         return Result;
      end New_Node;

      -----------------
      -- Set_Element --
      -----------------

      procedure Set_Element (Node : in out Node_Type) is
      begin
         Replace_Element (Node.E_Holder, New_Item);
      end Set_Element;

   --  Start of processing for Insert_Sans_Hint

   begin
      Conditional_Insert_Sans_Hint
        (Container,
         New_Item,
         Node,
         Inserted);
   end Insert_Sans_Hint;

   ----------------------
   -- Insert_With_Hint --
   ----------------------

   procedure Insert_With_Hint
     (Dst_Set  : in out Tree_Types.Tree_Type;
      Dst_Hint : Count_Type;
      Src_Node : Node_Type;
      Dst_Node : out Count_Type)
   is
      Success : Boolean;

      procedure Set_Element (Node : in out Node_Type);

      function New_Node return Count_Type;
      pragma Inline (New_Node);

      procedure Insert_Post is
        new Element_Keys.Generic_Insert_Post (New_Node);

      procedure Insert_Sans_Hint is
        new Element_Keys.Generic_Conditional_Insert (Insert_Post);

      procedure Local_Insert_With_Hint is
        new Element_Keys.Generic_Conditional_Insert_With_Hint
              (Insert_Post, Insert_Sans_Hint);

      procedure Allocate is new Generic_Allocate (Set_Element);

      --------------
      -- New_Node --
      --------------

      function New_Node return Count_Type is
         Result : Count_Type;
      begin
         Allocate (Dst_Set, Result);
         return Result;
      end New_Node;

      -----------------
      -- Set_Element --
      -----------------

      procedure Set_Element (Node : in out Node_Type) is
      begin
         Replace_Element (Node.E_Holder, Element (Src_Node.E_Holder));
      end Set_Element;

   --  Start of processing for Insert_With_Hint

   begin
      Local_Insert_With_Hint
        (Dst_Set,
         Dst_Hint,
         Element (Src_Node.E_Holder),
         Dst_Node,
         Success);
   end Insert_With_Hint;

   ------------------
   -- Intersection --
   ------------------

   procedure Intersection (Target : in out Set; Source : Set) is
   begin
      Set_Ops.Set_Intersection (Target.Content.all, Source.Content.all);
   end Intersection;

   function Intersection (Left, Right : Set) return Set is
   begin
      if Left'Address = Right'Address then
         return Copy (Left);
      end if;

      return S : Set do
         S.Content :=
           new Tree_Types.Tree_Type'(Set_Ops.Set_Intersection
                                       (Left.Content.all, Right.Content.all));
      end return;
   end Intersection;

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (Container : Set) return Boolean is
   begin
      return Length (Container) = 0;
   end Is_Empty;

   -----------------------------
   -- Is_Greater_Element_Node --
   -----------------------------

   function Is_Greater_Element_Node
     (Left  : Element_Type;
      Right : Node_Type) return Boolean
   is
   begin
      --  Compute e > node same as node < e

      return Element (Right.E_Holder) < Left;
   end Is_Greater_Element_Node;

   --------------------------
   -- Is_Less_Element_Node --
   --------------------------

   function Is_Less_Element_Node
     (Left  : Element_Type;
      Right : Node_Type) return Boolean
   is
   begin
      return Left < Element (Right.E_Holder);
   end Is_Less_Element_Node;

   -----------------------
   -- Is_Less_Node_Node --
   -----------------------

   function Is_Less_Node_Node (L, R : Node_Type) return Boolean is
   begin
      return Element (L.E_Holder) < Element (R.E_Holder);
   end Is_Less_Node_Node;

   ---------------
   -- Is_Subset --
   ---------------

   function Is_Subset (Subset : Set; Of_Set : Set) return Boolean is
   begin
      return Set_Ops.Set_Subset (Subset.Content.all, Of_Set.Content.all);
   end Is_Subset;

   ----------
   -- Last --
   ----------

   function Last (Container : Set) return Cursor is
   begin
      return (if Length (Container) = 0
              then No_Element
              else (Node => Container.Content.Last));
   end Last;

   ------------------
   -- Last_Element --
   ------------------

   function Last_Element (Container : Set) return Element_Type is
   begin
      if Last (Container).Node = 0 then
         raise Constraint_Error with "set is empty";
      end if;

      declare
         N : Tree_Types.Nodes_Type renames Container.Content.Nodes;
      begin
         return Element (N (Last (Container).Node).E_Holder);
      end;
   end Last_Element;

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

   function Length (Container : Set) return Count_Type is
   begin
      return Container.Content.Length;
   end Length;

   ----------
   -- Move --
   ----------

   procedure Move (Target : in out Set; Source : in out Set) is
   begin
      if Target'Address = Source'Address then
         return;
      end if;

      Clear (Target);

      Finalize (Target);

      Target.Content := Source.Content;
      Source.Content := Empty_Tree'Access;
   end Move;

   ----------
   -- Next --
   ----------

   function Next (Container : Set; Position : Cursor) return Cursor is
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

   procedure Next (Container : Set; Position : in out Cursor) is
   begin
      Position := Next (Container, Position);
   end Next;

   -------------
   -- Overlap --
   -------------

   function Overlap (Left, Right : Set) return Boolean is
   begin
      return Set_Ops.Set_Overlap (Left.Content.all, Right.Content.all);
   end Overlap;

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

   function Previous (Container : Set; Position : Cursor) return Cursor is
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
         return (if Node = 0 then No_Element else (Node => Node));
      end;
   end Previous;

   procedure Previous (Container : Set; Position : in out Cursor) is
   begin
      Position := Previous (Container, Position);
   end Previous;

   -------------
   -- Replace --
   -------------

   procedure Replace (Container : in out Set; New_Item : Element_Type) is
      Node : constant Count_Type :=
        Element_Keys.Find (Container.Content.all, New_Item);

   begin
      if Node = 0 then
         raise Constraint_Error with
           "attempt to replace element not in set";
      end if;

      Replace_Element (Container.Content.Nodes (Node).E_Holder, New_Item);
   end Replace;

   ---------------------
   -- Replace_Element --
   ---------------------

   procedure Replace_Element
     (Tree : in out Set;
      Node : Count_Type;
      Item : Element_Type)
   is
      pragma Assert (Node /= 0);

      function New_Node return Count_Type;
      pragma Inline (New_Node);

      procedure Local_Insert_Post is
        new Element_Keys.Generic_Insert_Post (New_Node);

      procedure Local_Insert_Sans_Hint is
        new Element_Keys.Generic_Conditional_Insert (Local_Insert_Post);

      procedure Local_Insert_With_Hint is
        new Element_Keys.Generic_Conditional_Insert_With_Hint
          (Local_Insert_Post,
           Local_Insert_Sans_Hint);

      NN : Tree_Types.Nodes_Type renames Tree.Content.Nodes;

      --------------
      -- New_Node --
      --------------

      function New_Node return Count_Type is
         N : Node_Type renames NN (Node);

      begin
         Replace_Element (N.E_Holder, Item);
         N.Color   := Red;
         N.Parent  := 0;
         N.Right   := 0;
         N.Left    := 0;
         return Node;
      end New_Node;

      Hint      : Count_Type;
      Result    : Count_Type;
      Inserted  : Boolean;

   --  Start of processing for Insert

   begin
      if Node > Length (Tree) then
         raise Program_Error with "Node does not exist";
      end if;

      if Item < Element (NN (Node).E_Holder)
        or else Element (NN (Node).E_Holder) < Item
      then
         null;
      else
         Replace_Element (NN (Node).E_Holder, Item);
         return;
      end if;

      Hint := Element_Keys.Ceiling (Tree.Content.all, Item);

      if Hint = 0 then
         null;

      elsif Item < Element (NN (Hint).E_Holder) then
         if Hint = Node then
            Replace_Element (NN (Node).E_Holder, Item);
            return;
         end if;

      else
         pragma Assert (not (Element (NN (Hint).E_Holder) < Item));
         raise Program_Error with "attempt to replace existing element";
      end if;

      Tree_Operations.Delete_Node_Sans_Free (Tree.Content.all, Node);

      Local_Insert_With_Hint
        (Tree     => Tree.Content.all,
         Position => Hint,
         Key      => Item,
         Node     => Result,
         Inserted => Inserted);

      pragma Assert (Inserted);
      pragma Assert (Result = Node);
   end Replace_Element;

   procedure Replace_Element
     (Container : in out Set;
      Position  : Cursor;
      New_Item  : Element_Type)
   is
   begin
      if not Has_Element (Container, Position) then
         raise Constraint_Error with
           "Position cursor has no element";
      end if;

      pragma Assert (Vet (Container.Content.all, Position.Node),
                     "bad cursor in Replace_Element");

      Replace_Element (Container, Position.Node, New_Item);
   end Replace_Element;

   ------------
   -- Resize --
   ------------

   procedure Resize (Container : in out Set; Size : Count_Type := 0) is
      Min_Size : constant Count_Type := 100;
      New_Size : constant Count_Type := Count_Type'Max (Min_Size, Size);

      CC : Tree_Access renames Container.Content;

   begin
      if CC = Empty_Tree'Access then
         CC := new Tree_Types.Tree_Type (New_Size);
         return;
      end if;

      if CC.Nodes'Length = Count_Type'Last then
         raise Constraint_Error with "Ordered Set already at size max";
      end if;

      if Size /= 0 and then CC.Capacity >= Size then
         return;
      end if;

      declare
         Next_Size : constant Count_Type :=
           (if CC.Nodes'Length < Count_Type'Last / 2
            then 2 * CC.Nodes'Length
            else Count_Type'Last);
         New_Tree : constant Tree_Access :=
           new Tree_Types.Tree_Type (Count_Type'Max (New_Size, Next_Size));

      begin

         --  Make a perfect copy of Container.Content

         New_Tree.First  := CC.First;
         New_Tree.Last   := CC.Last;
         New_Tree.Root   := CC.Root;
         New_Tree.Length := CC.Length;
         New_Tree.Free   := CC.Free;

         --  Copy the nodes. It is not possible to use an affectation
         --  because it wouild copy the element instead of moving them.

         for J in 1 .. CC.Capacity loop
            declare
               New_Node : Node_Type renames New_Tree.Nodes (J);
               Old_Node : Node_Type renames CC.Nodes (J);

            begin
               New_Node.Has_Element := Old_Node.Has_Element;
               New_Node.Parent      := Old_Node.Parent;
               New_Node.Left        := Old_Node.Left;
               New_Node.Right       := Old_Node.Right;
               New_Node.Color       := Old_Node.Color;
               Move (New_Node.E_Holder, Old_Node.E_Holder);
            end;
         end loop;

         --  Put the added node in the free list.
         --  It might be optimized by checking if New_Map.Free < 0 and,
         --  then just do nothing but it would make the unit relies on the
         --  current implementation of the Red Black Trees. A change in the
         --  Red Black Trees could thus create a sneaky bug here.

         for J in CC.Capacity + 1 .. New_Tree.Capacity loop
            New_Tree.Nodes (J).Has_Element := False;
            Tree_Operations.Free (New_Tree.all, J);
         end loop;

         Finalize (Container);
         CC := New_Tree;
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

   procedure Set_Color
     (Node  : in out Node_Type;
      Color : Red_Black_Trees.Color_Type)
   is
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

   --------------------------
   -- Symmetric_Difference --
   --------------------------

   procedure Symmetric_Difference (Target : in out Set; Source : Set) is
      L_Tar : constant Count_Type := Length (Target);
      L_Src : constant Count_Type := Length (Source);

   begin
      if Target.Content.Capacity - L_Tar < L_Src
      then
         declare
            Size : constant  Count_Type :=
              (if Count_Type'Last - L_Tar < L_Src
               then Count_Type'Last
               else L_Tar + L_Src);
         begin
            Resize (Target, Size);
         end;
      end if;

      Set_Ops.Set_Symmetric_Difference
        (Target.Content.all, Source.Content.all);
   end Symmetric_Difference;

   function Symmetric_Difference (Left, Right : Set) return Set is
   begin
      if Left'Address = Right'Address then
         return Empty_Set;
      end if;

      if Length (Right) = 0 then
         return Copy (Left);
      end if;

      if Length (Left) = 0 then
         return Copy (Right);
      end if;

      return S : Set do
         S.Content :=
           new Tree_Types.Tree_Type'(Set_Ops.Set_Symmetric_Difference
                                       (Left.Content.all,
                                        Right.Content.all));
      end return;
   end Symmetric_Difference;

   ------------
   -- To_Set --
   ------------

   function To_Set (New_Item : Element_Type) return Set is
      Node     : Cursor;
      Inserted : Boolean;

   begin
      return S : Set do
         Insert (S, New_Item, Node, Inserted);
         pragma Assert (Inserted);
      end return;
   end To_Set;

   -----------
   -- Union --
   -----------

   procedure Union (Target : in out Set; Source : Set) is
      L_Tar : constant Count_Type := Length (Target);
      L_Src : constant Count_Type := Length (Source);

   begin
      if L_Src = 0 then
         return;
      end if;
      if L_Tar = 0 then
         Assign (Target, Source);
      end if;

      if Target.Content.Capacity - L_Tar < L_Src
      then
         declare
            Size : constant  Count_Type :=
              (if Count_Type'Last - L_Tar < L_Src
               then Count_Type'Last
               else L_Tar + L_Src);
         begin
            Resize (Target, Size);
         end;
      end if;

      Set_Ops.Set_Union (Target.Content.all, Source.Content.all);
   end Union;

   function Union (Left, Right : Set) return Set is
   begin
      if Left'Address = Right'Address then
         return Copy (Left);
      end if;

      if Length (Left) = 0 then
         return Copy (Right);
      end if;

      if Length (Right) = 0 then
         return Copy (Left);
      end if;

      return S : Set do
         Assign (S, Source => Left);
         Union (S, Right);
      end return;
   end Union;

end SPARK.Containers.Formal.Unbounded_Ordered_Sets;
