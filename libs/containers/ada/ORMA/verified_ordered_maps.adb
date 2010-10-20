------------------------------------------------------------------------------
--                                                                          --
--                         GNAT LIBRARY COMPONENTS                          --
--                                                                          --
--  A D A . C O N T A I N E R S . B O U N D E D _ O R D E R E D _ M A P S   --
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

with Bounded_Red_Black_Trees.Generic_Operations;
pragma Elaborate_All
  (Bounded_Red_Black_Trees.Generic_Operations);

with Bounded_Red_Black_Trees.Generic_Keys;
pragma Elaborate_All (Bounded_Red_Black_Trees.Generic_Keys);

with System; use type System.Address;

package body Verified_Ordered_Maps is

   -----------------------------
   -- Node Access Subprograms --
   -----------------------------

   --  These subprograms provide a functional interface to access fields
   --  of a node, and a procedural interface for modifying these values.

   function Color (Tree : Tree_Type; Node : Node_Access) return Color_Type;
   pragma Inline (Color);

   function Left_Son (Tree : Tree_Type; Node : Count_Type) return Count_Type;
   pragma Inline (Left_Son);

   function Parent (Tree : Tree_Type; Node : Count_Type) return Count_Type;
   pragma Inline (Parent);

   function Right_Son (Tree : Tree_Type; Node : Count_Type) return Count_Type;
   pragma Inline (Right_Son);

   procedure Set_Parent
     (Tree   : in out Tree_Type;
      Node   : Node_Access;
      Parent : Node_Access);
   pragma Inline (Set_Parent);

   procedure Set_Left
     (Tree : in out Tree_Type;
      Node : Node_Access;
      Left : Node_Access);
   pragma Inline (Set_Left);

   procedure Set_Right
     (Tree  : in out Tree_Type;
      Node  : Node_Access;
      Right : Node_Access);
   pragma Inline (Set_Right);

   procedure Set_Color
     (Tree  : in out Tree_Type;
      Node  : Node_Access;
      Color : Color_Type);
   pragma Inline (Set_Color);

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Free (Tree : in out Tree_Type; X : in out Node_Access);

   generic
      with procedure Initialize (X : Node_Access);
   procedure Generic_Allocate_Node
     (Tree : in out Tree_Type;
      X    : out Count_Type);

   generic
     with procedure Allocate_Node (X : out Node_Access);
   procedure Generic_Append (Container : in out Tree_Type);

   function Is_Greater_Key_Node
     (Tree  : Tree_Type;
      Left  : Key_Type;
      Right : Node_Access) return Boolean;
   pragma Inline (Is_Greater_Key_Node);

   function Is_Less_Key_Node
     (Tree  : Tree_Type;
      Left  : Key_Type;
      Right : Node_Access) return Boolean;
   pragma Inline (Is_Less_Key_Node);

   function Next_Unchecked
     (Container : Map;
      Position : Count_Type) return Count_Type;

   --------------------------
   -- Local Instantiations --
   --------------------------

   package Tree_Operations is
      new Bounded_Red_Black_Trees.Generic_Operations
       (Tree_Type => Tree_Type,
        Left => Left_Son,
        Right => Right_Son);

   use Tree_Operations;

   package Key_Ops is
     new Bounded_Red_Black_Trees.Generic_Keys
       (Ops                 => Tree_Operations,
        Key_Type            => Key_Type,
        Is_Less_Key_Node    => Is_Less_Key_Node,
        Is_Greater_Key_Node => Is_Greater_Key_Node);

   ---------
   -- "=" --
   ---------

   function "=" (Left, Right : Map) return Boolean is
      Lst : Count_Type;
      Node : Count_Type := First(Left).Node;
      ENode : Count_Type;
   begin

      if Length(Left) /= Length(Right) then
         return False;
      end if;

      if Is_Empty(Left) then
         return True;
      end if;

      Lst := Next(Left.Tree.all, Last(Left).Node);
      while Node /= Lst loop
         ENode := Find(Right, Left.Tree.Nodes(Node).Key).Node;
         if ENode = 0 or else
           Left.Tree.Nodes(Node).Element /= Right.Tree.Nodes(ENode).Element then
            return False;
         end if;
         Node := Next(Left.Tree.all, Node);
      end loop;

      return True;

   end "=";

   ------------
   -- Assign --
   ------------

   procedure Assign (Target : in out Map; Source : Map) is
      procedure Append_Item_From_Source (Src_Node : Node_Access);

      procedure Append_Items_From_Source is
         new Tree_Operations.Generic_Iteration (Append_Item_From_Source);

      -----------------------------
      -- Append_Item_From_Source --
      -----------------------------

      procedure Append_Item_From_Source (Src_Node : Node_Access) is
         procedure Initialize (X : Node_Access);
         procedure Allocate_Node (X : out Node_Access);
         procedure Append is new Generic_Append (Allocate_Node);

         procedure Initialize (X : Node_Access) is
            S : Node_Type renames Source.Tree.Nodes (Src_Node);
            T : Node_Type renames Target.Tree.Nodes (X);
         begin
            T.Key := S.Key;
            T.Element := S.Element;
         end Initialize;

         procedure Allocate_Node is new Generic_Allocate_Node (Initialize);

         procedure Allocate_Node (X : out Node_Access) is
         begin
            Allocate_Node (Target.Tree.all, X);
         end Allocate_Node;

      --  Start of process for Assign

      begin
         Append (Target.Tree.all);
      end Append_Item_From_Source;

   begin
      if Target.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if Target'Address = Source'Address then
         return;
      end if;

      if Target.Capacity < Length(Source) then
         raise Storage_Error with "not enough capacity";  -- SE or CE? ???
      end if;

      Target.Clear;
      if Source.K = Plain then
         Append_Items_From_Source (Source.Tree.all);
      else
         declare
            X : Count_Type;
         begin
            X := Source.First;
            while X /= Next(Source.Tree.all, Source.Last) loop
               Append_Item_From_Source (X);
               X := Next(Source.Tree.all, X);
            end loop;
         end;
      end if;
   end Assign;

   -------------
   -- Ceiling --
   -------------

   function Ceiling (Container : Map; Key : Key_Type) return Cursor is
   begin

      if Container.K = Part then
         if Container.Length = 0 then
            return No_Element;
         end if;

         if Key < Container.Tree.Nodes(Container.First).Key then
            return (Node => Container.First);
         end if;

         if Container.Tree.Nodes(Container.Last).Key < Key then
            return No_Element;
         end if;
      end if;

      declare
         Node : constant Count_Type :=
           Key_Ops.Ceiling (Container.Tree.all, Key);

      begin
         if Node = 0 then
            return No_Element;
         end if;

         return (Node => Node);
      end;
   end Ceiling;

   -----------
   -- Clear --
   -----------

   procedure Clear (Container : in out Map) is
   begin
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      Tree_Operations.Clear (Container.Tree.all);
   end Clear;

   -----------
   -- Color --
   -----------

   function Color (Tree : Tree_Type; Node : Node_Access) return Color_Type is
   begin
      return Tree.Nodes (Node).Color;
   end Color;

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

   function Copy (Source : Map; Capacity : Count_Type := 0) return Map is
      Node : Count_Type := 1;
      N : Count_Type;
      Cu : Cursor;
   begin
      return Target : Map (Count_Type'Max (Source.Capacity, Capacity)) do
         if Length(Source) > 0 then
            Target.Tree.Length := Source.Tree.Length;
            Target.Tree.Root := Source.Tree.Root;
            Target.Tree.First := Source.Tree.First;
            Target.Tree.Last := Source.Tree.Last;
            Target.Tree.Free := Source.Tree.Free;

            while Node <= Source.Capacity loop
               Target.Tree.Nodes(Node).Element := Source.Tree.Nodes(Node).Element;
               Target.Tree.Nodes(Node).Key := Source.Tree.Nodes(Node).Key;
               Target.Tree.Nodes(Node).Parent := Source.Tree.Nodes(Node).Parent;
               Target.Tree.Nodes(Node).Left := Source.Tree.Nodes(Node).Left;
               Target.Tree.Nodes(Node).Right := Source.Tree.Nodes(Node).Right;
               Target.Tree.Nodes(Node).Color := Source.Tree.Nodes(Node).Color;
               Node := Node + 1;
            end loop;

            while Node <= Target.Capacity loop
               N := Node;
               Free(Tree => Target.Tree.all, X => N);
               Node := Node + 1;
            end loop;

            if Source.K = Part then
               Node := Target.Tree.First;
               while Node /= Source.First loop
                  Cu := (Node => Node);
                  Node := Next(Target.Tree.all, Node);
                  Delete(Target, Cu);
               end loop;

               Node := Next(Target.Tree.all, Source.Last);

               while Node /= 0 loop
                  Cu := (Node => Node);
                  Node := Next(Target.Tree.all, Node);
                  Delete(Target, Cu);
               end loop;
            end if;
         end if;
      end return;
   end Copy;

   ------------
   -- Delete --
   ------------

   procedure Delete (Container : in out Map; Position : in out Cursor) is
   begin
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if not Has_Element(Container, Position) then
         raise Constraint_Error with
           "Position cursor of Delete has no element";
      end if;

      pragma Assert (Vet (Container.Tree.all, Position.Node),
                     "Position cursor of Delete is bad");

      Tree_Operations.Delete_Node_Sans_Free (Container.Tree.all, Position.Node);
      Free (Container.Tree.all, Position.Node);
   end Delete;

   procedure Delete (Container : in out Map; Key : Key_Type) is
   begin
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;
      declare
         X : Node_Access := Key_Ops.Find (Container.Tree.all, Key);

      begin
         if X = 0 then
            raise Constraint_Error with "key not in map";
         end if;

         Tree_Operations.Delete_Node_Sans_Free (Container.Tree.all, X);
         Free (Container.Tree.all, X);
      end;
   end Delete;

   ------------------
   -- Delete_First --
   ------------------

   procedure Delete_First (Container : in out Map) is
      X : Node_Access := First(Container).Node;

   begin
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if X /= 0 then
         Tree_Operations.Delete_Node_Sans_Free (Container.Tree.all, X);
         Free (Container.Tree.all, X);
      end if;
   end Delete_First;

   -----------------
   -- Delete_Last --
   -----------------

   procedure Delete_Last (Container : in out Map) is
      X : Node_Access := Last(Container).Node;

   begin
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if X /= 0 then
         Tree_Operations.Delete_Node_Sans_Free (Container.Tree.all, X);
         Free (Container.Tree.all, X);
      end if;
   end Delete_Last;

   -------------
   -- Element --
   -------------

   function Element (Container : Map; Position : Cursor) return Element_Type is
   begin
      if not Has_Element(Container, Position) then
         raise Constraint_Error with
           "Position cursor of function Element has no element";
      end if;

      pragma Assert (Vet (Container.Tree.all, Position.Node),
                     "Position cursor of function Element is bad");

      return Container.Tree.Nodes (Position.Node).Element;

   end Element;

   function Element (Container : Map; Key : Key_Type) return Element_Type is
      Node : constant Node_Access := Find (Container, Key).Node;

   begin
      if Node = 0 then
         raise Constraint_Error with "key not in map";
      end if;

      return Container.Tree.Nodes (Node).Element;
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
      X : Node_Access := Key_Ops.Find (Container.Tree.all, Key);

   begin
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if X /= 0 then
         Tree_Operations.Delete_Node_Sans_Free (Container.Tree.all, X);
         Free (Container.Tree.all, X);
      end if;
   end Exclude;

   ----------
   -- Find --
   ----------

   function Find (Container : Map; Key : Key_Type) return Cursor is
   begin
      if Container.K = Part then
         if Container.Length = 0 then
            return No_Element;
         end if;

         if Key < Container.Tree.Nodes(Container.First).Key or
           Container.Tree.Nodes(Container.Last).Key < Key then
            return No_Element;
         end if;
      end if;

      declare
         Node : constant Count_Type :=
           Key_Ops.Find (Container.Tree.all, Key);

      begin
         if Node = 0 then
            return No_Element;
         end if;

         return (Node => Node);
      end;
   end Find;

   -----------
   -- First --
   -----------

   function First (Container : Map) return Cursor is
   begin
      if Length(Container) = 0 then
         return No_Element;
      end if;

      if Container.K = Plain then
         return (Node => Container.Tree.First);
      else
         return (Node => Container.First);
      end if;

   end First;

   -------------------
   -- First_Element --
   -------------------

   function First_Element (Container : Map) return Element_Type is
   begin
      if is_empty(Container) then
         raise Constraint_Error with "map is empty";
      end if;

      return Container.Tree.Nodes (First(Container).Node).Element;
   end First_Element;

   ---------------
   -- First_Key --
   ---------------

   function First_Key (Container : Map) return Key_Type is
   begin
      if is_empty(Container) then
         raise Constraint_Error with "map is empty";
      end if;

      return Container.Tree.Nodes (First(Container).Node).Key;
   end First_Key;

   -----------
   -- Floor --
   -----------

   function Floor (Container : Map; Key : Key_Type) return Cursor is
   begin

      if Container.K = Part then
         if Container.Length = 0 then
            return No_Element;
         end if;

         if Key < Container.Tree.Nodes(Container.First).Key then
            return No_Element;
         end if;

         if Container.Tree.Nodes(Container.Last).Key < Key then
            return (Node => Container.Last);
         end if;
      end if;

      declare
         Node : constant Count_Type :=
           Key_Ops.Floor (Container.Tree.all, Key);

      begin
         if Node = 0 then
            return No_Element;
         end if;

         return (Node => Node);
      end;
   end Floor;

   ----------
   -- Free --
   ----------

   procedure Free
     (Tree : in out Tree_Type;
      X    : in out Node_Access)
   is
      N : Nodes_Type renames Tree.Nodes;

   begin
      if X = 0 then
         return;
      end if;

      pragma Assert (X in N'Range);

      N (X).Parent := -1;
      N (X).Left := X;

      if Tree.Length = 0 then

         N (X).Right := X;
         X := 0;

         return;
      end if;

      pragma Assert (Tree.Free <= N'Last);

      pragma Assert (Tree.First in N'Range);
      pragma Assert (Tree.First /= X);
      pragma Assert (N (Tree.First).Left = 0);

      pragma Assert (Tree.Last in N'Range);
      pragma Assert (Tree.Last /= X);
      pragma Assert (N (Tree.Last).Right = 0);

      pragma Assert (Tree.Root in N'Range);
      pragma Assert (Tree.Root /= X);
      pragma Assert (N (Tree.Root).Parent = 0);

      N (X).Right := Tree.Free;
      Tree.Free := X;
      X := 0;
   end Free;

   ---------------------------
   -- Generic_Allocate_Node --
   ---------------------------

   procedure Generic_Allocate_Node
     (Tree : in out Tree_Type;
      X    : out Count_Type)
   is
      N : Nodes_Type renames Tree.Nodes;

   begin
      if Tree.Length >= Tree.Capacity then
         raise Storage_Error with "not enough capacity";
      end if;

      if Tree.Length = 0
        or else Tree.Free = 0
      then
         X := Tree.Length + 1;
         Initialize (X);
         Tree.Free := 0;  -- we're allocating from initialized storage

      else
         pragma Assert (Tree.Free in N'Range);

         X := Tree.Free;
         Initialize (X);
         Tree.Free := N (X).Right;
      end if;

      N (X).Parent := 0;
      N (X).Right := 0;
      N (X).Left := 0;
      N (X).Color := Bounded_Red_Black_Trees.Red;
   end Generic_Allocate_Node;

   --------------------
   -- Generic_Append --
   --------------------

   procedure Generic_Append (Container : in out Tree_Type) is
      function New_Node return Count_Type;

      procedure Insert_Sans_Hint
        (Tree     : in out Tree_Type;
         Key      : Key_Type;
         Node     : out Count_Type;
         Inserted : out Boolean);

      X : Count_Type;

      function New_Node return Count_Type is
      begin
         return X;
      end New_Node;

      procedure Insert_Post is
        new Key_Ops.Generic_Insert_Post (New_Node);

      --  This can be optimized away, since we know Insert_With_Hint with
      --  always succeed (items in the stream are in key order), and therefore
      --  we know insert_sans_hint will never be called. ???
      procedure Insert_Sans_Hint
        (Tree     : in out Tree_Type;
         Key      : Key_Type;
         Node     : out Count_Type;
         Inserted : out Boolean)
      is
         pragma Unreferenced (Tree);
         pragma Unreferenced (Key);
      begin
         pragma Assert (False);
         Node := Count_Type'Last;
         Inserted := False;
      end Insert_Sans_Hint;

      procedure Local_Insert_With_Hint is
        new Key_Ops.Generic_Conditional_Insert_With_Hint
          (Insert_Post,
           Insert_Sans_Hint);

      Y : Count_Type;
      B : Boolean;

   --  Start of processing for Append

   begin
      Allocate_Node (X);

      Local_Insert_With_Hint
        (Tree     => Container,
         Position => 0,  --  begin search assuming large key
         Key      => Container.Nodes (X).Key,
         Node     => Y,
         Inserted => B);

      pragma Assert (B);
      pragma Assert (Y = X);
   end Generic_Append;

   -----------------
   -- Has_Element --
   -----------------

   function Has_Element (Container : Map; Position : Cursor) return Boolean is
   begin
      if Position.Node = 0 then
         return False;
      end if;

      if Container.Tree.Nodes(Position.Node).Parent < 0 then
         return False;
      end if;

      if Container.K = Plain then
         return True;
      end if;

      declare
         Key : Key_Type := Container.Tree.Nodes(Position.Node).Key;
      begin

         if Key < Container.Tree.Nodes(Container.First).Key or
           Container.Tree.Nodes(Container.Last).Key < Key then
            return False;
         end if;

         return True;
      end;
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
         if Container.Tree.Lock > 0 then
            raise Program_Error with
              "attempt to tamper with cursors (map is locked)";
         end if;

         declare
            N : Node_Type renames Container.Tree.Nodes (Position.Node);
         begin
            N.Key := Key;
            N.Element := New_Item;
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
   begin
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      declare
         function New_Node return Node_Access;

         procedure Insert_Post is
           new Key_Ops.Generic_Insert_Post (New_Node);

         procedure Insert_Sans_Hint is
           new Key_Ops.Generic_Conditional_Insert (Insert_Post);

         --------------
         -- New_Node --
         --------------

         function New_Node return Node_Access is
            procedure Initialize (X : Node_Access);
            procedure Allocate_Node is new Generic_Allocate_Node (Initialize);

            procedure Initialize (X : Node_Access) is
               N : Node_Type renames Container.Tree.Nodes (X);
            begin
               N.Key := Key;
               N.Element := New_Item;
            end Initialize;

            X : Node_Access;

         begin
            Allocate_Node (Container.Tree.all, X);
            return X;
         end New_Node;

         --  Start of processing for Insert

      begin
         Insert_Sans_Hint
           (Container.Tree.all,
            Key,
            Position.Node,
            Inserted);
      end;
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

   ------------
   -- Insert --
   ------------

   procedure Insert
     (Container : in out Map;
      Key       : Key_Type;
      Position  : out Cursor;
      Inserted  : out Boolean)
   is
   begin
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      declare
         function New_Node return Node_Access;

         procedure Insert_Post is
           new Key_Ops.Generic_Insert_Post (New_Node);

         procedure Insert_Sans_Hint is
           new Key_Ops.Generic_Conditional_Insert (Insert_Post);

         --------------
         -- New_Node --
         --------------

         function New_Node return Node_Access is
            procedure Initialize (X : Node_Access);
            procedure Allocate_Node is new Generic_Allocate_Node (Initialize);

            procedure Initialize (X : Node_Access) is
               N : Node_Type renames Container.Tree.Nodes (X);
            begin
               N.Key := Key;
            end Initialize;

            X : Node_Access;

         begin
            Allocate_Node (Container.Tree.all, X);
            return X;
         end New_Node;

         --  Start of processing for Insert

      begin
         Insert_Sans_Hint
           (Container.Tree.all,
            Key,
            Position.Node,
            Inserted);
      end;
   end Insert;

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (Container : Map) return Boolean is
   begin
      return Length(Container) = 0;
   end Is_Empty;

   -------------------------
   -- Is_Greater_Key_Node --
   -------------------------

   function Is_Greater_Key_Node
     (Tree  : Tree_Type;
      Left  : Key_Type;
      Right : Node_Access) return Boolean
   is
   begin
      --  k > node same as node < k

      return Tree.Nodes (Right).Key < Left;
   end Is_Greater_Key_Node;

   ----------------------
   -- Is_Less_Key_Node --
   ----------------------

   function Is_Less_Key_Node
     (Tree  : Tree_Type;
      Left  : Key_Type;
      Right : Node_Access) return Boolean
   is
   begin
      return Left < Tree.Nodes (Right).Key;
   end Is_Less_Key_Node;

   -------------
   -- Iterate --
   -------------

   procedure Iterate
     (Container : Map;
      Process   : not null access procedure (Container : Map; Position : Cursor))
   is
      procedure Process_Node (Node : Node_Access);
      pragma Inline (Process_Node);

      procedure Local_Iterate is
         new Tree_Operations.Generic_Iteration (Process_Node);

      ------------------
      -- Process_Node --
      ------------------

      procedure Process_Node (Node : Node_Access) is
      begin
         Process (Container, (Node => Node));
      end Process_Node;

      B : Natural renames Container.Tree.all.Busy;

   --  Start of processing for Iterate

   begin
      B := B + 1;

      begin

         if Container.K = Plain then
            Local_Iterate (Container.Tree.all);
            return;
         end if;

         if Container.Length = 0 then
            return;
         end if;


         declare
            FElt : Key_Type := Container.Tree.Nodes(Container.First).Key;
            TElt : Key_Type := Container.Tree.Nodes(Container.Last).Key;

            procedure Iterate (P : Count_Type) is
               X : Count_Type := P;
            begin
               while X /= 0 loop
                  if Container.Tree.Nodes(X).Key < FElt then
                     X := Container.Tree.Nodes(X).Right;
                  elsif TElt < Container.Tree.Nodes(X).Key then
                     X := Container.Tree.Nodes(X).Left;
                  else
                     Iterate(Container.Tree.Nodes(X).Left);
                     Process_Node(X);
                     X := Container.Tree.Nodes(X).Right;
                  end if;
               end loop;
            end Iterate;

         begin
            Iterate (Container.Tree.Root);
         end;

      exception
         when others =>
            B := B - 1;
            raise;
      end;

      B := B - 1;
   end Iterate;

   ---------
   -- Key --
   ---------

   function Key (Container : Map; Position : Cursor) return Key_Type is
   begin
      if not Has_Element(Container, Position) then
         raise Constraint_Error with
           "Position cursor of function Key has no element";
      end if;

      pragma Assert (Vet (Container.Tree.all, Position.Node),
                     "Position cursor of function Key is bad");

      return Container.Tree.Nodes (Position.Node).Key;
   end Key;

   ----------
   -- Last --
   ----------

   function Last (Container : Map) return Cursor is
   begin
      if Length(Container) = 0 then
         return No_Element;
      end if;

      if Container.K = Plain then
         return (Node => Container.Tree.Last);
      end if;

      return (Node => Container.Last);
   end Last;

   ------------------
   -- Last_Element --
   ------------------

   function Last_Element (Container : Map) return Element_Type is
   begin
      if Is_Empty(Container) then
         raise Constraint_Error with "map is empty";
      end if;

      return Container.Tree.Nodes (Last(Container).Node).Element;
   end Last_Element;

   --------------
   -- Last_Key --
   --------------

   function Last_Key (Container : Map) return Key_Type is
   begin
      if Is_Empty(Container) then
         raise Constraint_Error with "map is empty";
      end if;

      return Container.Tree.Nodes (Last(Container).Node).Key;
   end Last_Key;

   ----------
   -- Left --
   ----------

   function Left (Container : Map; Position : Cursor) return Map is
      Lst : Count_Type;
      Fst : constant Count_Type := First(Container).Node;
      L : Count_Type := 0;
      C : Count_Type := Fst;
   begin
      while C /= Position.Node loop
         if C = Last(Container).Node or C = 0 then
            raise Constraint_Error with
              "Position cursor has no element";
         end if;
         Lst := C;
         C := Next(Container.Tree.all, C);
         L := L + 1;
      end loop;
      if L = 0 then
         return (Capacity => Container.Capacity,
                 K => Part,
                 Tree => Container.Tree,
                 Length => 0,
                 First => 0,
                 Last => 0);
      else
         return (Capacity => Container.Capacity,
                 K => Part,
                 Tree => Container.Tree,
                 Length => L,
                 First => Fst,
                 Last => Lst);
      end if;
   end Left;

   --------------
   -- Left_Son --
   --------------

   function Left_Son (Tree : Tree_Type; Node : Node_Access) return Node_Access is
   begin
      return Tree.Nodes (Node).Left;
   end Left_Son;

   ------------
   -- Length --
   ------------

   function Length (Container : Map) return Count_Type is
   begin
      if Container.K = Plain then
         return Container.Tree.Length;
      else
         return Container.Length;
      end if;
   end Length;

   ----------
   -- Move --
   ----------

   procedure Move (Target : in out Map; Source : in out Map) is
      NN : Nodes_Type renames Source.Tree.Nodes;
      X  : Node_Access;

   begin
      if Target.K /= Plain or Source.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if Target'Address = Source'Address then
         return;
      end if;

      if Target.Capacity < Length(Source) then
         raise Constraint_Error with  -- ???
           "Source length exceeds Target capacity";
      end if;

      if Source.Tree.Busy > 0 then
         raise Program_Error with
           "attempt to tamper with cursors of Source (list is busy)";
      end if;

      Clear (Target);

      loop
         X := First(Source).Node;
         exit when X = 0;

         --  Here we insert a copy of the source element into the target, and
         --  then delete the element from the source.  Another possibility is
         --  that delete it first (and hang onto its index), then insert it.
         --  ???

         Insert (Target, NN (X).Key, NN (X).Element);  -- optimize???

         Tree_Operations.Delete_Node_Sans_Free (Source.Tree.all, X);
         Free (Source.Tree.all, X);
      end loop;
   end Move;

   ----------
   -- Next --
   ----------

   function Next_Unchecked (Container : Map; Position : Count_Type) return Count_Type is
   begin

      if Container.K = Part and then
        (Container.Length = 0 or Position = Container.Last) then
         return 0;
      end if;

      return Tree_Operations.Next (Container.Tree.all, Position);
   end Next_Unchecked;

   procedure Next (Container : Map; Position : in out Cursor) is
   begin
      Position := Next (Container, Position);
   end Next;

   function Next (Container : Map; Position : Cursor) return Cursor is
   begin
      if Position = No_Element then
         return No_Element;
      end if;

      if not Has_Element(Container, Position) then
         raise Constraint_Error;
      end if;

      pragma Assert (Vet (Container.Tree.all, Position.Node),
                     "bad cursor in Next");

      return (Node => Next_Unchecked(Container, Position.Node));
   end Next;

   -------------
   -- Overlap --
   -------------

   function Overlap (Left, Right : Map) return Boolean is
   begin

      if Length(Left) = 0 or Length(Right) = 0 then
         return False;
      end if;

      declare

         L_Node : Count_Type := First(Left).Node;
         R_Node : Count_Type := First(Right).Node;

         L_Last : constant Count_Type := Next(Left.Tree.all, Last(Left).Node);
         R_Last : constant Count_Type := Next(Right.Tree.all, Last(Right).Node);

      begin
         if Left'Address = Right'Address then
            return True;
         end if;

         loop
            if L_Node = L_Last
              or else R_Node = R_Last
            then
               return False;
            end if;

            if Left.Tree.Nodes(L_Node).Key < Right.Tree.Nodes(R_Node).Key then
               L_Node := Next (Left.Tree.all, L_Node);

            elsif Right.Tree.Nodes(R_Node).Key < Left.Tree.Nodes(L_Node).Key then
               R_Node := Next (Right.Tree.all, R_Node);

            else
               return True;
            end if;
         end loop;
      end;
   end Overlap;

   ------------
   -- Parent --
   ------------

   function Parent (Tree : Tree_Type; Node : Node_Access) return Node_Access is
   begin
      return Tree.Nodes (Node).Parent;
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

      if not Has_Element(Container, Position) then
         raise Constraint_Error;
      end if;

      pragma Assert (Vet (Container.Tree.all, Position.Node),
                     "bad cursor in Previous");

      if Container.K = Part and then
        (Container.Length = 0 or Position.Node = Container.First) then
         return No_Element;
      end if;

      declare
         Tree : Tree_Type renames Container.Tree.all;
         Node : constant Count_Type :=
                  Tree_Operations.Previous (Tree, Position.Node);

      begin
         if Node = 0 then
            return No_Element;
         end if;

         return (Node => Node);
      end;
   end Previous;

   -------------------
   -- Query_Element --
   -------------------

   procedure Query_Element
     (Container : in out Map;
      Position : Cursor;
      Process  : not null access procedure (Key     : Key_Type;
                                            Element : Element_Type))
   is
   begin
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if not Has_Element(Container, Position) then
         raise Constraint_Error with
           "Position cursor of Query_Element has no element";
      end if;

      pragma Assert (Vet (Container.Tree.all, Position.Node),
                     "Position cursor of Query_Element is bad");

      declare
         T : Tree_Type renames Container.Tree.all;

         B : Natural renames T.Busy;
         L : Natural renames T.Lock;

      begin
         B := B + 1;
         L := L + 1;

         declare
            N  : Node_Type renames T.Nodes (Position.Node);
            K : Key_Type renames N.Key;
            E : Element_Type renames N.Element;

         begin
            Process (K, E);
         exception
            when others =>
               L := L - 1;
               B := B - 1;
               raise;
         end;

         L := L - 1;
         B := B - 1;
      end;
   end Query_Element;

   ----------
   -- Read --
   ----------

   procedure Read
     (Stream    : not null access Root_Stream_Type'Class;
      Container : out Map)
   is
      procedure Initialize (X : Node_Access);
      pragma Inline (Initialize);

      procedure Allocate_Node (X : out Node_Access);
      pragma Inline (Allocate_Node);

      procedure Append is new Generic_Append (Allocate_Node);

      procedure Initialize (X : Node_Access) is
         N : Node_Type renames Container.Tree.Nodes (X);
      begin
         Key_Type'Read (Stream, N.Key);
         Element_Type'Read (Stream, N.Element);
      end Initialize;

      procedure Allocate_Node is new Generic_Allocate_Node (Initialize);

      procedure Allocate_Node (X : out Node_Access) is
      begin
         Allocate_Node (Container.Tree.all, X);
      end Allocate_Node;

      N : Count_Type'Base;

   --  Start of processing for Read

   begin
      Container.Clear;  -- clear before or after storage check???

      Count_Type'Base'Read (Stream, N);

      if N < 0 then
         raise Program_Error with "stream appears to be corrupt";
      end if;

      if N = 0 then
         return;
      end if;

      if N > Container.Capacity then  --  check here???
         raise Storage_Error with "not enough capacity";  -- ???
      end if;

      for Indx in 1 .. N loop
         Append (Container.Tree.all);
      end loop;
   end Read;

   procedure Read
     (Stream : not null access Root_Stream_Type'Class;
      Item   : out Cursor)
   is
   begin
      raise Program_Error with "attempt to stream map cursor";
   end Read;

   -------------
   -- Replace --
   -------------

   procedure Replace
     (Container : in out Map;
      Key       : Key_Type;
      New_Item  : Element_Type)
   is
   begin

      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      declare
         Node : constant Node_Access := Key_Ops.Find (Container.Tree.all, Key);

      begin
         if Node = 0 then
            raise Constraint_Error with "key not in map";
         end if;

         if Container.Tree.Lock > 0 then
            raise Program_Error with
              "attempt to tamper with cursors (map is locked)";
         end if;

         declare
            N : Node_Type renames Container.Tree.Nodes (Node);
         begin
            N.Key := Key;
            N.Element := New_Item;
         end;
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
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if not Has_Element(Container, Position) then
         raise Constraint_Error with
           "Position cursor of Replace_Element has no element";
      end if;

      if Container.Tree.Lock > 0 then
         raise Program_Error with
           "attempt to tamper with cursors (map is locked)";
      end if;

      pragma Assert (Vet (Container.Tree.all, Position.Node),
                     "Position cursor of Replace_Element is bad");

      Container.Tree.Nodes (Position.Node).Element := New_Item;
   end Replace_Element;

   ---------------------
   -- Reverse_Iterate --
   ---------------------

   procedure Reverse_Iterate
     (Container : Map;
      Process   : not null access procedure (Container : Map; Position : Cursor))
   is
      procedure Process_Node (Node : Node_Access);
      pragma Inline (Process_Node);

      procedure Local_Reverse_Iterate is
         new Tree_Operations.Generic_Reverse_Iteration (Process_Node);

      ------------------
      -- Process_Node --
      ------------------

      procedure Process_Node (Node : Node_Access) is
      begin
         Process (Container, (Node => Node));
      end Process_Node;

      B : Natural renames Container.Tree.Busy;

      --  Start of processing for Reverse_Iterate

   begin
      B := B + 1;

      begin

         if Container.K = Plain then
            Local_Reverse_Iterate (Container.Tree.all);
            return;
         end if;

         if Container.Length = 0 then
            return;
         end if;


         declare
            FElt : Key_Type := Container.Tree.Nodes(Container.First).Key;
            TElt : Key_Type := Container.Tree.Nodes(Container.Last).Key;

            procedure Iterate (P : Count_Type) is
               X : Count_Type := P;
            begin
               while X /= 0 loop
                  if Container.Tree.Nodes(X).Key < FElt then
                     X := Container.Tree.Nodes(X).Right;
                  elsif TElt < Container.Tree.Nodes(X).Key then
                     X := Container.Tree.Nodes(X).Left;
                  else
                     Iterate(Container.Tree.Nodes(X).Right);
                     Process_Node(X);
                     X := Container.Tree.Nodes(X).Left;
                  end if;
               end loop;
            end Iterate;

         begin
            Iterate (Container.Tree.Root);
         end;

      exception
         when others =>
            B := B - 1;
            raise;
      end;

      B := B - 1;
   end Reverse_Iterate;

   -----------
   -- Right --
   -----------

   function Right (Container : Map; Position : Cursor) return Map is
      Lst : Count_Type;
      L : Count_Type := 0;
      C : Count_Type := Position.Node;
   begin

      if C = 0 then
         return (Capacity => Container.Capacity,
                 K => Part,
                 Tree => Container.Tree,
                 Length => 0,
                 First => 0,
                 Last => 0);
      end if;

      if Container.K = Plain then
         Lst := 0;
      else
         Lst := Next(Container.Tree.all, Container.Last);
      end if;

      if C = Lst then
         raise Constraint_Error with
           "Position cursor has no element";
      end if;

      while C /= Lst loop
         if C = 0 then
            raise Constraint_Error with
              "Position cursor has no element";
         end if;
         C := Next(Container.Tree.all, C);
         L := L + 1;
      end loop;

      return (Capacity => Container.Capacity,
              K => Part,
              Tree => Container.Tree,
              Length => L,
              First => Position.Node,
              Last => Last(Container).Node);
   end Right;

   ---------------
   -- Right_Son --
   ---------------

   function Right_Son (Tree : Tree_Type; Node : Node_Access) return Node_Access is
   begin
      return Tree.Nodes (Node).Right;
   end Right_Son;

   ---------------
   -- Set_Color --
   ---------------

   procedure Set_Color
     (Tree  : in out Tree_Type;
      Node  : Node_Access;
      Color : Color_Type)
   is
   begin
      Tree.Nodes (Node).Color := Color;
   end Set_Color;

   --------------
   -- Set_Left --
   --------------

   procedure Set_Left
     (Tree : in out Tree_Type;
      Node : Node_Access;
      Left : Node_Access)
   is
   begin
      Tree.Nodes (Node).Left := Left;
   end Set_Left;

   ----------------
   -- Set_Parent --
   ----------------

   procedure Set_Parent
     (Tree   : in out Tree_Type;
      Node   : Node_Access;
      Parent : Node_Access)
   is
   begin
      Tree.Nodes (Node).Parent := Parent;
   end Set_Parent;

   ---------------
   -- Set_Right --
   ---------------

   procedure Set_Right
     (Tree  : in out Tree_Type;
      Node  : Node_Access;
      Right : Node_Access)
   is
   begin
      Tree.Nodes (Node).Right := Right;
   end Set_Right;

   ------------------
   -- Strict_Equal --
   ------------------

   function Strict_Equal (Left, Right : Map) return Boolean is
      LNode : Count_Type := First(Left).Node;
      RNode : Count_Type := First(Right).Node;
   begin
      if Length(Left) /= Length(Right) then
         return False;
      end if;

      while LNode = RNode loop
         if LNode = 0 then
            return True;
         end if;

         if Left.Tree.Nodes(LNode).Element /= Right.Tree.Nodes(RNode).Element or
         Left.Tree.Nodes(LNode).Key /= Right.Tree.Nodes(RNode).Key then
            exit;
         end if;

         LNode := Next_Unchecked(Left, LNode);
         RNode := Next_Unchecked(Right, RNode);
      end loop;
      return False;
   end Strict_Equal;

   --------------------
   -- Update_Element --
   --------------------

   procedure Update_Element
     (Container : in out Map;
      Position  : Cursor;
      Process   : not null access procedure (Key     : Key_Type;
                                             Element : in out Element_Type))
   is
   begin
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if not Has_Element(Container, Position) then
         raise Constraint_Error with
           "Position cursor of Update_Element has no element";
      end if;

      pragma Assert (Vet (Container.Tree.all, Position.Node),
                     "Position cursor of Update_Element is bad");

      declare
         T : Tree_Type renames Container.Tree.all;

         B : Natural renames T.Busy;
         L : Natural renames T.Lock;

      begin
         B := B + 1;
         L := L + 1;

         declare
            N : Node_Type renames T.Nodes (Position.Node);
            K : Key_Type renames N.Key;
            E : Element_Type renames N.Element;

         begin
            Process (K, E);
         exception
            when others =>
               L := L - 1;
               B := B - 1;
               raise;
         end;

         L := L - 1;
         B := B - 1;
      end;
   end Update_Element;

   -----------
   -- Write --
   -----------

   procedure Write
     (Stream    : not null access Root_Stream_Type'Class;
      Container : Map)
   is
      procedure Write_Node
        (Stream : not null access Root_Stream_Type'Class;
         Node   : Node_Access);
      pragma Inline (Write_Node);

      procedure Write is
         new Tree_Operations.Generic_Write (Write_Node);

      ----------------
      -- Write_Node --
      ----------------

      procedure Write_Node
        (Stream : not null access Root_Stream_Type'Class;
         Node   : Node_Access)
      is
         N : Node_Type renames Container.Tree.Nodes (Node);
      begin
         Key_Type'Write (Stream, N.Key);
         Element_Type'Write (Stream, N.Element);
      end Write_Node;

   --  Start of processing for Write

   begin
      Write (Stream, Container.Tree.all);
   end Write;

   procedure Write
     (Stream : not null access Root_Stream_Type'Class;
      Item   : Cursor)
   is
   begin
      raise Program_Error with "attempt to stream map cursor";
   end Write;

end Verified_Ordered_Maps;
