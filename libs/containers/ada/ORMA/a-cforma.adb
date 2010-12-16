------------------------------------------------------------------------------
--                                                                          --
--                         GNAT LIBRARY COMPONENTS                          --
--                                                                          --
--   A D A . C O N T A I N E R S . F O R M A L _ O R D E R E D _ M A P S    --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--          Copyright (C) 2010, Free Software Foundation, Inc.              --
--                                                                          --
-- GNAT is free software;  you can  redistribute it  and/or modify it under --
-- terms of the  GNU General Public License as published  by the Free Soft- --
-- ware  Foundation;  either version 3,  or (at your option) any later ver- --
-- sion.  GNAT is distributed in the hope that it will be useful, but WITH- --
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
------------------------------------------------------------------------------

with Ada.Containers.Red_Black_Trees.Generic_Bounded_Operations;
pragma Elaborate_All
  (Ada.Containers.Red_Black_Trees.Generic_Bounded_Operations);

with Ada.Containers.Red_Black_Trees.Generic_Bounded_Keys;
pragma Elaborate_All (Ada.Containers.Red_Black_Trees.Generic_Bounded_Keys);

with System; use type System.Address;

package body Ada.Containers.Formal_Ordered_Maps is

   -----------------------------
   -- Node Access Subprograms --
   -----------------------------

   --  These subprograms provide a functional interface to access fields
   --  of a node, and a procedural interface for modifying these values.

   function Color (Node : Node_Type)
                   return Ada.Containers.Red_Black_Trees.Color_Type;
   pragma Inline (Color);

   function Left_Son (Node : Node_Type) return Count_Type;
   pragma Inline (Left);

   function Parent (Node : Node_Type) return Count_Type;
   pragma Inline (Parent);

   function Right_Son (Node : Node_Type) return Count_Type;
   pragma Inline (Right);

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

   procedure Free (Tree : in out Map; X : Count_Type);

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

   package Tree_Operations is
     new Red_Black_Trees.Generic_Bounded_Operations
       (Tree_Types => Tree_Types,
        Left      => Left_Son,
        Right     => Right_Son);

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
      Node  : Count_Type := First (Left).Node;
      ENode : Count_Type;
   begin

      if Length (Left) /= Length (Right) then
         return False;
      end if;

      if Is_Empty (Left) then
         return True;
      end if;

      Lst := Next (Left, Last (Left).Node);
      while Node /= Lst loop
         ENode := Find (Right, Left.Nodes (Node).Key).Node;
         if ENode = 0 or else
           Left.Nodes (Node).Element /= Right.Nodes (ENode).Element
         then
            return False;
         end if;
         Node := Next (Left, Node);
      end loop;

      return True;

   end "=";

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
         SN : Node_Type renames Source.Nodes (Source_Node);

         procedure Set_Element (Node : in out Node_Type);
         pragma Inline (Set_Element);

         function New_Node return Count_Type;
         pragma Inline (New_Node);

         procedure Insert_Post is
            new Key_Ops.Generic_Insert_Post (New_Node);

         procedure Unconditional_Insert_Sans_Hint is
            new Key_Ops.Generic_Unconditional_Insert (Insert_Post);

         procedure Unconditional_Insert_Avec_Hint is
            new Key_Ops.Generic_Unconditional_Insert_With_Hint
              (Insert_Post,
               Unconditional_Insert_Sans_Hint);

         procedure Allocate is
            new Generic_Allocate (Set_Element);

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
            Node.Key := SN.Key;
            Node.Element := SN.Element;
         end Set_Element;

         Target_Node : Count_Type;

      --  Start of processing for Append_Element

      begin
         Unconditional_Insert_Avec_Hint
           (Tree  => Target,
            Hint  => 0,
            Key   => SN.Key,
            Node  => Target_Node);
      end Append_Element;

   --  Start of processing for Assign

   begin

      if Target'Address = Source'Address then
         return;
      end if;

      if Target.Capacity < Length (Source) then
         raise Storage_Error with "not enough capacity";  -- SE or CE? ???
      end if;

      Tree_Operations.Clear_Tree (Target);
      Append_Elements (Source);
   end Assign;

   -------------
   -- Ceiling --
   -------------

   function Ceiling (Container : Map; Key : Key_Type) return Cursor is

      Node : constant Count_Type :=
        Key_Ops.Ceiling (Container, Key);

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

      Tree_Operations.Clear_Tree (Container);
   end Clear;

   -----------
   -- Color --
   -----------

   function Color (Node : Node_Type) return Color_Type is
   begin
      return Node.Color;
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
      N    : Count_Type;
   begin
      return Target : Map (Count_Type'Max (Source.Capacity, Capacity)) do
         if Length (Source) > 0 then
            Target.Length := Source.Length;
            Target.Root := Source.Root;
            Target.First := Source.First;
            Target.Last := Source.Last;
            Target.Free := Source.Free;

            while Node <= Source.Capacity loop
               Target.Nodes (Node).Element :=
                 Source.Nodes (Node).Element;
               Target.Nodes (Node).Key :=
                 Source.Nodes (Node).Key;
               Target.Nodes (Node).Parent :=
                 Source.Nodes (Node).Parent;
               Target.Nodes (Node).Left :=
                 Source.Nodes (Node).Left;
               Target.Nodes (Node).Right :=
                 Source.Nodes (Node).Right;
               Target.Nodes (Node).Color :=
                 Source.Nodes (Node).Color;
               Target.Nodes (Node).Has_Element :=
                 Source.Nodes (Node).Has_Element;
               Node := Node + 1;
            end loop;

            while Node <= Target.Capacity loop
               N := Node;
               Formal_Ordered_Maps.Free (Tree => Target, X => N);
               Node := Node + 1;
            end loop;
         end if;
      end return;
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

      pragma Assert (Vet (Container, Position.Node),
                     "Position cursor of Delete is bad");

      Tree_Operations.Delete_Node_Sans_Free (Container,
                                             Position.Node);
      Formal_Ordered_Maps.Free (Container, Position.Node);
   end Delete;

   procedure Delete (Container : in out Map; Key : Key_Type) is

      X : constant Node_Access := Key_Ops.Find (Container, Key);

   begin
      if X = 0 then
         raise Constraint_Error with "key not in map";
      end if;

      Tree_Operations.Delete_Node_Sans_Free (Container, X);
      Formal_Ordered_Maps.Free (Container, X);
   end Delete;

   ------------------
   -- Delete_First --
   ------------------

   procedure Delete_First (Container : in out Map) is
      X : constant Node_Access := First (Container).Node;

   begin

      if X /= 0 then
         Tree_Operations.Delete_Node_Sans_Free (Container, X);
         Formal_Ordered_Maps.Free (Container, X);
      end if;
   end Delete_First;

   -----------------
   -- Delete_Last --
   -----------------

   procedure Delete_Last (Container : in out Map) is
      X : constant Node_Access := Last (Container).Node;

   begin

      if X /= 0 then
         Tree_Operations.Delete_Node_Sans_Free (Container, X);
         Formal_Ordered_Maps.Free (Container, X);
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

      pragma Assert (Vet (Container, Position.Node),
                     "Position cursor of function Element is bad");

      return Container.Nodes (Position.Node).Element;

   end Element;

   function Element (Container : Map; Key : Key_Type) return Element_Type is
      Node : constant Node_Access := Find (Container, Key).Node;

   begin
      if Node = 0 then
         raise Constraint_Error with "key not in map";
      end if;

      return Container.Nodes (Node).Element;
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
      X : constant Node_Access := Key_Ops.Find (Container, Key);

   begin

      if X /= 0 then
         Tree_Operations.Delete_Node_Sans_Free (Container, X);
         Formal_Ordered_Maps.Free (Container, X);
      end if;
   end Exclude;

   ----------
   -- Find --
   ----------

   function Find (Container : Map; Key : Key_Type) return Cursor is

      Node : constant Count_Type :=
        Key_Ops.Find (Container, Key);

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

      return (Node => Container.First);

   end First;

   -------------------
   -- First_Element --
   -------------------

   function First_Element (Container : Map) return Element_Type is
   begin
      if Is_Empty (Container) then
         raise Constraint_Error with "map is empty";
      end if;

      return Container.Nodes (First (Container).Node).Element;
   end First_Element;

   ---------------
   -- First_Key --
   ---------------

   function First_Key (Container : Map) return Key_Type is
   begin
      if Is_Empty (Container) then
         raise Constraint_Error with "map is empty";
      end if;

      return Container.Nodes (First (Container).Node).Key;
   end First_Key;

   -----------
   -- Floor --
   -----------

   function Floor (Container : Map; Key : Key_Type) return Cursor is

      Node : constant Count_Type :=
        Key_Ops.Floor (Container, Key);

   begin
      if Node = 0 then
         return No_Element;
      end if;

      return (Node => Node);
   end Floor;

   ----------
   -- Free --
   ----------

   procedure Free
     (Tree : in out Map;
      X  : Count_Type)
   is
   begin
      Tree.Nodes (X).Has_Element := False;
      Tree_Operations.Free (Tree, X);
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
      if Position.Node = 0 then
         return False;
      end if;

      return Container.Nodes (Position.Node).Has_Element;
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
         if Container.Lock > 0 then
            raise Program_Error with
              "attempt to tamper with cursors (map is locked)";
         end if;

         declare
            N : Node_Type renames Container.Nodes (Position.Node);
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
      function New_Node return Node_Access;

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
            Node.Key := Key;
            Node.Element := New_Item;
         end Initialize;

         X : Node_Access;

      begin
         Allocate_Node (Container, X);
         return X;
      end New_Node;

      --  Start of processing for Insert

   begin
      Insert_Sans_Hint
        (Container,
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

   ------------
   -- Insert --
   ------------

   procedure Insert
     (Container : in out Map;
      Key       : Key_Type;
      Position  : out Cursor;
      Inserted  : out Boolean)
   is
      function New_Node return Node_Access;

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
            Node.Key := Key;
         end Initialize;

         X : Node_Access;

      begin
         Allocate_Node (Container, X);
         return X;
      end New_Node;

      --  Start of processing for Insert

   begin
      Insert_Sans_Hint
        (Container,
         Key,
         Position.Node,
         Inserted);
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

      return Right.Key < Left;
   end Is_Greater_Key_Node;

   ----------------------
   -- Is_Less_Key_Node --
   ----------------------

   function Is_Less_Key_Node
     (Left  : Key_Type;
      Right : Node_Type) return Boolean
   is
   begin
      return Left < Right.Key;
   end Is_Less_Key_Node;

   -------------
   -- Iterate --
   -------------

   procedure Iterate
     (Container : Map;
      Process   :
        not null access procedure (Container : Map; Position : Cursor))
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

      B : Natural renames Container'Unrestricted_Access.Busy;

      --  Start of processing for Iterate

   begin
      B := B + 1;

      begin
         Local_Iterate (Container);
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
      if not Has_Element (Container, Position) then
         raise Constraint_Error with
           "Position cursor of function Key has no element";
      end if;

      pragma Assert (Vet (Container, Position.Node),
                     "Position cursor of function Key is bad");

      return Container.Nodes (Position.Node).Key;
   end Key;

   ----------
   -- Last --
   ----------

   function Last (Container : Map) return Cursor is
   begin
      if Length (Container) = 0 then
         return No_Element;
      end if;
      return (Node => Container.Last);
   end Last;

   ------------------
   -- Last_Element --
   ------------------

   function Last_Element (Container : Map) return Element_Type is
   begin
      if Is_Empty (Container) then
         raise Constraint_Error with "map is empty";
      end if;

      return Container.Nodes (Last (Container).Node).Element;
   end Last_Element;

   --------------
   -- Last_Key --
   --------------

   function Last_Key (Container : Map) return Key_Type is
   begin
      if Is_Empty (Container) then
         raise Constraint_Error with "map is empty";
      end if;

      return Container.Nodes (Last (Container).Node).Key;
   end Last_Key;

   ----------
   -- Left --
   ----------

   function Left (Container : Map; Position : Cursor) return Map is
      Curs : Cursor := Position;
      C : Map (Container.Capacity) :=
        Copy (Container, Container.Capacity);
      Node : Count_Type;
   begin
      if Curs = No_Element then
         return C;
      end if;
      if not Has_Element (Container, Curs) then
         raise Constraint_Error;
      end if;

      while Curs.Node /= 0 loop
         Node := Curs.Node;
         Delete (C, Curs);
         Curs := Next (Container, (Node => Node));
      end loop;
      return C;
   end Left;

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
      return Container.Length;
   end Length;

   ----------
   -- Move --
   ----------

   procedure Move (Target : in out Map; Source : in out Map) is
      NN : Tree_Types.Nodes_Type renames Source.Nodes;
      X  : Node_Access;

   begin

      if Target'Address = Source'Address then
         return;
      end if;

      if Target.Capacity < Length (Source) then
         raise Constraint_Error with  -- ???
           "Source length exceeds Target capacity";
      end if;

      if Source.Busy > 0 then
         raise Program_Error with
           "attempt to tamper with cursors of Source (list is busy)";
      end if;

      Clear (Target);

      loop
         X := First (Source).Node;
         exit when X = 0;

         --  Here we insert a copy of the source element into the target, and
         --  then delete the element from the source.  Another possibility is
         --  that delete it first (and hang onto its index), then insert it.
         --  ???

         Insert (Target, NN (X).Key, NN (X).Element);  -- optimize???

         Tree_Operations.Delete_Node_Sans_Free (Source, X);
         Formal_Ordered_Maps.Free (Source, X);
      end loop;
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

      pragma Assert (Vet (Container, Position.Node),
                     "bad cursor in Next");

      return (Node => Tree_Operations.Next (Container, Position.Node));
   end Next;

   -------------
   -- Overlap --
   -------------

   function Overlap (Left, Right : Map) return Boolean is
   begin

      if Length (Left) = 0 or Length (Right) = 0 then
         return False;
      end if;

      declare

         L_Node : Count_Type := First (Left).Node;
         R_Node : Count_Type := First (Right).Node;

         L_Last : constant Count_Type :=
                    Next (Left, Last (Left).Node);
         R_Last : constant Count_Type :=
                    Next (Right, Last (Right).Node);

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

            if Left.Nodes (L_Node).Key
              < Right.Nodes (R_Node).Key then
               L_Node := Next (Left, L_Node);
            elsif Right.Nodes (R_Node).Key
              < Left.Nodes (L_Node).Key then
               R_Node := Next (Right, R_Node);

            else
               return True;
            end if;
         end loop;
      end;
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

      pragma Assert (Vet (Container, Position.Node),
                     "bad cursor in Previous");

      declare
         Node : constant Count_Type :=
                  Tree_Operations.Previous (Container, Position.Node);

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
      Position  : Cursor;
      Process   : not null access procedure (Key     : Key_Type;
                                             Element : Element_Type))
   is
   begin

      if not Has_Element (Container, Position) then
         raise Constraint_Error with
           "Position cursor of Query_Element has no element";
      end if;

      pragma Assert (Vet (Container, Position.Node),
                     "Position cursor of Query_Element is bad");

      declare

         B : Natural renames Container.Busy;
         L : Natural renames Container.Lock;

      begin
         B := B + 1;
         L := L + 1;

         declare
            N  : Node_Type renames Container.Nodes (Position.Node);
            K  : Key_Type renames N.Key;
            E  : Element_Type renames N.Element;

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
      procedure Read_Element (Node : in out Node_Type);
      pragma Inline (Read_Element);

      procedure Allocate is
         new Generic_Allocate (Read_Element);

      procedure Read_Elements is
         new Tree_Operations.Generic_Read (Allocate);

      ------------------
      -- Read_Element --
      ------------------

      procedure Read_Element (Node : in out Node_Type) is
      begin
         Key_Type'Read (Stream, Node.Key);
         Element_Type'Read (Stream, Node.Element);
      end Read_Element;

      --  Start of processing for Read
   begin

      Read_Elements (Stream, Container);
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

      declare
         Node : constant Node_Access := Key_Ops.Find (Container, Key);

      begin
         if Node = 0 then
            raise Constraint_Error with "key not in map";
         end if;

         if Container.Lock > 0 then
            raise Program_Error with
              "attempt to tamper with cursors (map is locked)";
         end if;

         declare
            N : Node_Type renames Container.Nodes (Node);
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

      if not Has_Element (Container, Position) then
         raise Constraint_Error with
           "Position cursor of Replace_Element has no element";
      end if;

      if Container.Lock > 0 then
         raise Program_Error with
           "attempt to tamper with cursors (map is locked)";
      end if;

      pragma Assert (Vet (Container, Position.Node),
                     "Position cursor of Replace_Element is bad");

      Container.Nodes (Position.Node).Element := New_Item;
   end Replace_Element;

   ---------------------
   -- Reverse_Iterate --
   ---------------------

   procedure Reverse_Iterate
     (Container : Map;
      Process   :
        not null access procedure (Container : Map; Position : Cursor))
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

      B : Natural renames Container'Unrestricted_Access.Busy;

      --  Start of processing for Reverse_Iterate

   begin
      B := B + 1;

      begin
         Local_Reverse_Iterate (Container);

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
      Curs : Cursor := First (Container);
      C : Map (Container.Capacity) :=
        Copy (Container, Container.Capacity);
      Node : Count_Type;
   begin
      if Curs = No_Element then
         Clear (C);
         return C;
      end if;
      if Position /= No_Element and not Has_Element (Container, Position) then
         raise Constraint_Error;
      end if;

      while Curs.Node /= Position.Node loop
         Node := Curs.Node;
         Delete (C, Curs);
         Curs := Next (Container, (Node => Node));
      end loop;
      return C;
   end Right;

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
      Color : Color_Type)
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

   ------------------
   -- Strict_Equal --
   ------------------

   function Strict_Equal (Left, Right : Map) return Boolean is
      LNode : Count_Type := First (Left).Node;
      RNode : Count_Type := First (Right).Node;
   begin
      if Length (Left) /= Length (Right) then
         return False;
      end if;

      while LNode = RNode loop
         if LNode = 0 then
            return True;
         end if;

         if Left.Nodes (LNode).Element /=
           Right.Nodes (RNode).Element or
           Left.Nodes (LNode).Key /= Right.Nodes (RNode).Key then
            exit;
         end if;

         LNode := Next (Left, LNode);
         RNode := Next (Right, RNode);
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

      if not Has_Element (Container, Position) then
         raise Constraint_Error with
           "Position cursor of Update_Element has no element";
      end if;

      pragma Assert (Vet (Container, Position.Node),
                     "Position cursor of Update_Element is bad");

      declare

         B : Natural renames Container.Busy;
         L : Natural renames Container.Lock;

      begin
         B := B + 1;
         L := L + 1;

         declare
            N : Node_Type renames Container.Nodes (Position.Node);
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
         Node   : Node_Type);
      pragma Inline (Write_Node);

      procedure Write_Nodes is
         new Tree_Operations.Generic_Write (Write_Node);

      ----------------
      -- Write_Node --
      ----------------

      procedure Write_Node
        (Stream : not null access Root_Stream_Type'Class;
         Node   : Node_Type)
      is
      begin
         Key_Type'Write (Stream, Node.Key);
         Element_Type'Write (Stream, Node.Element);
      end Write_Node;

   --  Start of processing for Write

   begin
      Write_Nodes (Stream, Container);
   end Write;

   procedure Write
     (Stream : not null access Root_Stream_Type'Class;
      Item   : Cursor)
   is
   begin
      raise Program_Error with "attempt to stream map cursor";
   end Write;

end Ada.Containers.Formal_Ordered_Maps;
