------------------------------------------------------------------------------
--                                                                          --
--                         GNAT LIBRARY COMPONENTS                          --
--                                                                          --
--   A D A . C O N T A I N E R S . B O U N D E D _ H A S H E D _ M A P S    --
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

with Verified_Hash_Tables.Generic_Operations;
pragma Elaborate_All (Verified_Hash_Tables.Generic_Operations);

with Verified_Hash_Tables.Generic_Keys;
pragma Elaborate_All (Verified_Hash_Tables.Generic_Keys);

with System;  use type System.Address;

package body Verified_Hashed_Maps is

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Equivalent_Key_Node
     (Key  : Key_Type;
      HT   : Hash_Table_Type;
      Node : Node_Access) return Boolean;
   pragma Inline (Equivalent_Key_Node);

   function Hash_Node
     (HT   : Hash_Table_Type;
      Node : Node_Access) return Hash_Type;
   pragma Inline (Hash_Node);

   function Get_Next
     (HT   : Hash_Table_Type;
      Node : Node_Access) return Node_Access;
   pragma Inline (Get_Next);

   function Next_Unchecked
     (Container : Map;
      Position : Cursor) return Cursor;

   procedure Set_Has_Element
     (HT   : in out Hash_Table_Type;
      Node : Node_Access;
      Has_Element : Boolean);
   pragma Inline (Set_Has_Element);

   procedure Set_Next
     (HT   : in out Hash_Table_Type;
      Node : Node_Access;
      Next : Node_Access);
   pragma Inline (Set_Next);

   function Vet (Container : Map; Position : Cursor) return Boolean;

   --------------------------
   -- Local Instantiations --
   --------------------------

   package HT_Ops is
      new Verified_Hash_Tables.Generic_Operations
       (HT_Types  => HT_Types,
        Hash_Node => Hash_Node,
        Get_Next  => Get_Next,
        Set_Next  => Set_Next,
        Set_Has_Element => Set_Has_Element);

   package Key_Ops is
      new Verified_Hash_Tables.Generic_Keys
       (HT_Types  => HT_Types,
        Get_Next  => Get_Next,
        Set_Next  => Set_Next,
        Key_Type  => Key_Type,
        Hash      => Hash,
        Equivalent_Keys => Equivalent_Key_Node);

   ---------
   -- "=" --
   ---------

   function "=" (Left, Right : Map) return Boolean is
      CuL : Cursor := First(Left);
      CuR : Cursor := First(Right);
   begin
      if Length(Left) /= Length(Right) then
         return false;
      end if;

      while CuL.Node /= 0 or CuR.Node /= 0 loop
         if CuL.Node /= CuR.Node or else
           (Left.HT.Nodes(CuL.Node).Element /= Right.HT.Nodes(CuR.Node).Element or
            Left.HT.Nodes(CuL.Node).Key /= Right.HT.Nodes(CuR.Node).Key) then
            return False;
         end if;
         CuL := Next_Unchecked(Left, CuL);
         CuR := Next_Unchecked(Right, CuR);
      end loop;

      return True;
   end "=";

   ------------
   -- Assign --
   ------------

   procedure Assign (Target : in out Map; Source : Map) is
      procedure Insert_Element (Source_Node : Node_Access);
      pragma Inline (Insert_Element);

      procedure Insert_Elements is
         new HT_Ops.Generic_Iteration (Insert_Element);

      --------------------
      -- Insert_Element --
      --------------------

      procedure Insert_Element (Source_Node : Node_Access) is
         N : Node_Type renames Source.HT.Nodes (Source_Node);
      begin
         Target.Insert (N.Key, N.Element);
      end Insert_Element;

   --  Start of processing for Assign

   begin
      if Target.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if Target'Address = Source'Address then
         return;
      end if;

      if Target.Capacity < Length(Source) then
         raise Constraint_Error with  -- correct exception ???
           "Source length exceeds Target capacity";
      end if;

      Clear (Target);  -- checks busy bits

      case Source.K is
         when Plain =>
            Insert_Elements (Source.HT.all);
         when Part =>
            declare
               N : Count_Type := Source.First;
            begin
               while N /= HT_Ops.Next(Source.HT.all, Source.Last) loop
                  Insert_Element(N);
                  N := HT_Ops.Next(Source.HT.all, N);
               end loop;
            end;
      end case;
   end Assign;

   --------------
   -- Capacity --
   --------------

   function Capacity (Container : Map) return Count_Type is
   begin
      return Container.HT.Nodes'Length;
   end Capacity;

   -----------
   -- Clear --
   -----------

   procedure Clear (Container : in out Map) is
   begin

      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      HT_Ops.Clear (Container.HT.all);
   end Clear;

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

   function Copy
     (Source   : Map;
      Capacity : Count_Type := 0;
      Modulus  : Hash_Type := 0) return Map
   is
      C : constant Count_Type := Count_Type'Max (Capacity, Source.Capacity);
      H : Hash_Type := 1;
      N : Count_Type := 1;
      Target : Map(C, Source.Modulus);
      Cu : Cursor;
   begin
      if (Source.K = Part and Source.Length = 0) or
        Source.HT.Length = 0 then
         return Target;
      end if;

      Target.HT.Length := Source.HT.Length;
      Target.HT.Free := Source.HT.Free;
      while H<=Source.Modulus loop
         Target.HT.Buckets(H) := Source.HT.Buckets(H);
         H := H+1;
      end loop;
      while N<=Source.Capacity loop
         Target.HT.Nodes(N) := Source.HT.Nodes(N);
         N := N+1;
      end loop;
      while N <= C loop
         Cu := (Node => N);
         HT_Ops.Free(Target.HT.all, Cu.Node);
         N := N+1;
      end loop;
      if Source.K = Part then
         N := HT_Ops.First(Target.HT.all);
         while N /= Source.First loop
            Cu := (Node => N);
            N := HT_Ops.Next(Target.HT.all,N);
            Delete(Target, Cu);
         end loop;
         N := HT_Ops.Next(Target.HT.all, Source.Last);
         while N /= 0 loop
            Cu := (Node => N);
            N := HT_Ops.Next(Target.HT.all,N);
            Delete(Target, Cu);
         end loop;
      end if;
      return Target;
   end Copy;

   ---------------------
   -- Default_Modulus --
   ---------------------

   function Default_Modulus (Capacity : Count_Type) return Hash_Type is
   begin
      return HT_Ops.Default_Modulus (Capacity);
   end Default_Modulus;

   ------------
   -- Delete --
   ------------

   procedure Delete (Container : in out Map; Key : Key_Type) is
      X : Node_Access;

   begin

      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      Key_Ops.Delete_Key_Sans_Free (Container.HT.all, Key, X);

      if X = 0 then
         raise Constraint_Error with "attempt to delete key not in map";
      end if;

      HT_Ops.Free (Container.HT.all, X);
   end Delete;

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

      if Container.HT.Busy > 0 then
         raise Program_Error with
           "Delete attempted to tamper with elements (map is busy)";
      end if;

      pragma Assert (Vet (Container, Position), "bad cursor in Delete");

      HT_Ops.Delete_Node_Sans_Free (Container.HT.all, Position.Node);

      HT_Ops.Free (Container.HT.all, Position.Node);
   end Delete;

   -------------
   -- Element --
   -------------

   function Element (Container : Map; Key : Key_Type) return Element_Type is
      Node : constant Node_Access := Key_Ops.Find (Container.HT.all, Key);

   begin
      if Node = 0 then
         raise Constraint_Error with
           "no element available because key not in map";
      end if;

      return Container.HT.Nodes (Node).Element;
   end Element;

   function Element (Container : Map; Position : Cursor) return Element_Type is
   begin
      if not Has_Element(Container, Position) then
         raise Constraint_Error with "Position cursor equals No_Element";
      end if;

      pragma Assert (Vet (Container, Position), "bad cursor in function Element");

      return Container.HT.Nodes (Position.Node).Element;
   end Element;

   -------------------------
   -- Equivalent_Key_Node --
   -------------------------

   function Equivalent_Key_Node
     (Key  : Key_Type;
      HT   : Hash_Table_Type;
      Node : Node_Access) return Boolean is
   begin
      return Equivalent_Keys (Key, HT.Nodes (Node).Key);
   end Equivalent_Key_Node;

   ---------------------
   -- Equivalent_Keys --
   ---------------------

   function Equivalent_Keys (Left : Map; CLeft : Cursor;
                             Right : Map; CRight : Cursor)
     return Boolean is
   begin
      if not Has_Element(Left, CLeft) then
         raise Constraint_Error with
           "Left cursor of Equivalent_Keys has no element";
      end if;

      if not Has_Element(Right, CRight) then
         raise Constraint_Error with
           "Right cursor of Equivalent_Keys has no element";
      end if;

      pragma Assert (Vet (Left, CLeft), "Left cursor of Equivalent_Keys is bad");
      pragma Assert (Vet (Right, CRight), "Right cursor of Equivalent_Keys is bad");

      declare
         LT : Hash_Table_Type renames Left.HT.all;
         RT : Hash_Table_Type renames Right.HT.all;

         LN : Node_Type renames LT.Nodes (CLeft.Node);
         RN : Node_Type renames RT.Nodes (CRight.Node);

      begin
         return Equivalent_Keys (LN.Key, RN.Key);
      end;
   end Equivalent_Keys;

   function Equivalent_Keys (Left : Map; CLeft : Cursor; Right : Key_Type) return Boolean is
   begin
      if not Has_Element(Left, CLeft) then
         raise Constraint_Error with
           "Left cursor of Equivalent_Keys has no element";
      end if;

      pragma Assert (Vet (Left, CLeft), "Left cursor in Equivalent_Keys is bad");

      declare
         LT : Hash_Table_Type renames Left.HT.all;
         LN : Node_Type renames LT.Nodes (CLeft.Node);

      begin
         return Equivalent_Keys (LN.Key, Right);
      end;
   end Equivalent_Keys;

   function Equivalent_Keys (Left : Key_Type; Right : Map; CRight : Cursor) return Boolean is
   begin
      if Has_Element(Right, CRight) then
         raise Constraint_Error with
           "Right cursor of Equivalent_Keys has no element";
      end if;

      pragma Assert (Vet (Right, CRight), "Right cursor of Equivalent_Keys is bad");

      declare
         RT : Hash_Table_Type renames Right.HT.all;
         RN : Node_Type renames RT.Nodes (CRight.Node);

      begin
         return Equivalent_Keys (Left, RN.Key);
      end;
   end Equivalent_Keys;

   -------------
   -- Exclude --
   -------------

   procedure Exclude (Container : in out Map; Key : Key_Type) is
      X : Node_Access;
   begin

      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      Key_Ops.Delete_Key_Sans_Free (Container.HT.all, Key, X);
      HT_Ops.Free (Container.HT.all, X);
   end Exclude;

   ----------
   -- Find --
   ----------

   function Find (Container : Map; Key : Key_Type) return Cursor is
   begin
      case Container.K is
         when Plain =>
            declare
               Node : constant Node_Access := Key_Ops.Find (Container.HT.all, Key);

            begin
               if Node = 0 then
                  return No_Element;
               end if;

               return (Node => Node);
            end;
         when Part =>
            declare
               function Find_Between
                 (HT  : Hash_Table_Type;
                  Key : Key_Type;
                  From : Count_Type;
                  To : Count_Type) return Node_Access is

                  Indx : Hash_Type;
                  Indx_From : Hash_Type := Key_Ops.Index (HT, HT.Nodes(From).Key);
                  Indx_To : Hash_Type := Key_Ops.Index (HT, HT.Nodes(To).Key);
                  Node : Node_Access;
                  To_Node : Node_Access;

               begin

                  Indx := Key_Ops.Index (HT, Key);

                  if Indx < Indx_From or Indx > Indx_To then
                     return 0;
                  end if;

                  if Indx = Indx_From then
                     Node := From;
                  else
                     Node := HT.Buckets (Indx);
                  end if;

                  if Indx = Indx_To then
                     To_Node := HT.Nodes(To).Next;
                  else
                     To_Node := 0;
                  end if;

                  while Node /= To_Node loop
                     if Equivalent_Key_Node (Key, HT, Node) then
                        return Node;
                     end if;
                     Node := HT.Nodes(Node).Next;
                  end loop;
                  return 0;
               end Find_Between;
            begin

               if Container.Length = 0 then
                  return No_Element;
               end if;

               return (Node => Find_Between(Container.HT.all, Key,
                       Container.First, Container.Last));
            end;
      end case;
   end Find;

   -----------
   -- First --
   -----------

   function First (Container : Map) return Cursor is
   begin
      case Container.K is
         when Plain =>
            declare
               Node : constant Node_Access := HT_Ops.First (Container.HT.all);

            begin
               if Node = 0 then
                  return No_Element;
               end if;

               return (Node => Node);
            end;
         when Part =>
            declare
               Node : constant Count_Type := Container.First;

            begin
               if Node = 0 then
                  return No_Element;
               end if;

               return (Node => Node);
            end;
      end case;
   end First;

   --------------
   -- Get_Next --
   --------------

   function Get_Next
     (HT   : Hash_Table_Type;
      Node : Node_Access) return Node_Access is
   begin
      return HT.Nodes (Node).Next;
   end Get_Next;

   -----------------
   -- Has_Element --
   -----------------

   function Has_Element (Container : Map; Position : Cursor) return Boolean is
   begin
      if Position.Node = 0 or else
        not Container.HT.Nodes(Position.Node).Has_Element then
         return False;
      end if;

      if Container.K = Plain then
         return true;
      end if;

      declare
         Lst_Index : Hash_Type :=
           Key_Ops.Index(Container.HT.all,
                              Container.HT.Nodes(Container.Last).Key);
         Fst_Index : Hash_Type :=
           Key_Ops.Index(Container.HT.all,
                              Container.HT.Nodes(Container.First).Key);
         Index : Hash_Type :=
           Key_Ops.Index(Container.HT.all,
                              Container.HT.Nodes(Position.Node).Key);
         Lst_Node : Count_Type;
         Node : Count_Type;
      begin

         if Index < Fst_Index or Index > Lst_Index then
            return False;
         end if;

         if Index > Fst_Index and Index < Lst_Index then
            return True;
         end if;

         if Index = Fst_Index then
            Node := Container.First;
         else
            Node := Container.HT.Buckets(Index);
         end if;

         if Index = Lst_Index then
            Lst_Node := Container.HT.Nodes(Container.Last).Next;
         else
            Lst_Node := 0;
         end if;

         while Node /= Lst_Node loop
            if Position.Node = Node then
               return True;
            end if;
            Node := HT_Ops.Next(Container.HT.all, Node);
         end loop;

         return False;
      end;
   end Has_Element;

   ---------------
   -- Hash_Node --
   ---------------

   function Hash_Node
     (HT   : Hash_Table_Type;
      Node : Node_Access) return Hash_Type is
   begin
      return Hash (HT.Nodes (Node).Key);
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
         if Container.HT.Lock > 0 then
            raise Program_Error with
              "Include attempted to tamper with cursors (map is locked)";
         end if;

         declare
            N : Node_Type renames Container.HT.Nodes (Position.Node);
         begin
            N.Key := Key;
            N.Element := New_Item;
         end;
      end if;
   end Include;

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

         HT : Hash_Table_Type renames Container.HT.all;

         function New_Node (Next : Node_Access) return Node_Access;
         pragma Inline (New_Node);

         procedure Local_Insert is
           new Key_Ops.Generic_Conditional_Insert (New_Node);

         procedure Initialize_Node (N : in out Node_Type);
         pragma Inline (Initialize_Node);

         procedure Allocate_Node is
           new HT_Ops.Generic_Allocate_Node (Initialize_Node);

         --------------
         -- New_Node --
         --------------

         function New_Node (Next : Node_Access) return Node_Access is
            X : Node_Access;
         begin
            Allocate_Node (HT, X);
            HT.Nodes (X).Next := Next;
            return X;
         end New_Node;

         ---------------------
         -- Initialize_Node --
         ---------------------

         procedure Initialize_Node (N : in out Node_Type) is
            E : Element_Type;  -- better way to make default ???
            pragma Warnings (Off, E);

         begin
            N.Key := Key;
            N.Element := E;
         end Initialize_Node;

         --  Start of processing for Insert

      begin
         Local_Insert (HT, Key, Position.Node, Inserted);
      end;
   end Insert;

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
         HT : Hash_Table_Type renames Container.HT.all;

         function New_Node (Next : Node_Access) return Node_Access;
         pragma Inline (New_Node);

         procedure Local_Insert is
           new Key_Ops.Generic_Conditional_Insert (New_Node);

         procedure Initialize_Node (N : in out Node_Type);
         pragma Inline (Initialize_Node);

         procedure Allocate_Node is
           new HT_Ops.Generic_Allocate_Node (Initialize_Node);

         --------------
         -- New_Node --
         --------------

         function New_Node (Next : Node_Access) return Node_Access is
            X : Node_Access;
         begin
            Allocate_Node (HT, X);
            HT.Nodes (X).Next := Next;
            return X;
         end New_Node;

         ---------------------
         -- Initialize_Node --
         ---------------------

         procedure Initialize_Node (N : in out Node_Type) is
         begin
            N.Key := Key;
            N.Element := New_Item;
            N.Has_Element := True;
         end Initialize_Node;

         --  Start of processing for Insert

      begin
         Local_Insert (HT, Key, Position.Node, Inserted);
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
         raise Constraint_Error with
           "attempt to insert key already in map";
      end if;
   end Insert;

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (Container : Map) return Boolean is
   begin
      return Length(Container) = 0;
   end Is_Empty;

   -------------
   -- Iterate --
   -------------

   procedure Iterate
     (Container : Map;
      Process   : not null access procedure (Container : Map; Position : Cursor))
   is
      procedure Process_Node (Node : Node_Access);
      pragma Inline (Process_Node);

      procedure Local_Iterate is new HT_Ops.Generic_Iteration (Process_Node);

      ------------------
      -- Process_Node --
      ------------------

      procedure Process_Node (Node : Node_Access) is
      begin
         Process (Container, (Node => Node));
      end Process_Node;

      B : Natural renames Container'Unrestricted_Access.HT.Busy;

   --  Start of processing for Iterate

   begin
      B := B + 1;

      begin
         case Container.K is
            when Plain =>
               Local_Iterate (Container.HT.all);
            when Part =>

               if Container.Length = 0 then
                  return;
               end if;

               declare
                  Node : Count_Type := Container.First;
               begin
                  while Node /= Container.HT.Nodes(Container.Last).Next loop
                     Process_Node(Node);
                     Node := HT_Ops.Next(Container.HT.all, Node);
                  end loop;
               end;
         end case;
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

      pragma Assert (Vet (Container, Position), "bad cursor in function Key");

      return Container.HT.Nodes (Position.Node).Key;
   end Key;

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
         if C = 0 or C = Container.Last then
            raise Constraint_Error with
              "Position cursor has no element";
         end if;
         Lst := C;
         C := HT_Ops.Next(Container.HT.all, C);
         L := L + 1;
      end loop;
      if L = 0 then
         return (Capacity => Container.Capacity,
                 Modulus => Container.Modulus,
                 K => Part,
                 HT => Container.HT,
                 Length => 0,
                 First => 0,
                 Last => 0);
      else
         return (Capacity => Container.Capacity,
                 Modulus => Container.Modulus,
                 K => Part,
                 HT => Container.HT,
                 Length => L,
                 First => Fst,
                 Last => Lst);
      end if;
   end Left;


   ------------
   -- Length --
   ------------

   function Length (Container : Map) return Count_Type is
   begin
      case Container.K is
         when Plain =>
            return Container.HT.Length;
         when Part =>
            return Container.Length;
      end case;
   end Length;

   ----------
   -- Move --
   ----------

   procedure Move
     (Target : in out Map;
      Source : in out Map)
   is
      HT   : HT_Types.Hash_Table_Type renames Source.HT.all;
      NN   : HT_Types.Nodes_Type renames HT.Nodes;
      X, Y : Node_Access;

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

      if HT.Busy > 0 then
         raise Program_Error with
           "attempt to tamper with cursors of Source (list is busy)";
      end if;

      Clear (Target);

      if HT.Length = 0 then
         return;
      end if;

      X := HT_Ops.First (HT);
      while X /= 0 loop
         Insert (Target, NN (X).Key, NN (X).Element);  -- optimize???

         Y := HT_Ops.Next (HT, X);

         HT_Ops.Delete_Node_Sans_Free (HT, X);
         HT_Ops.Free (HT, X);

         X := Y;
      end loop;
   end Move;

   ----------
   -- Next --
   ----------

   function Next_Unchecked (Container : Map; Position : Cursor) return Cursor is
      HT   : Hash_Table_Type renames Container.HT.all;
      Node : constant Node_Access := HT_Ops.Next (HT, Position.Node);

   begin
      if Node = 0 then
         return No_Element;
      end if;

      if Container.K = Part and then Container.Last = Position.Node then
         return No_Element;
      end if;

      return (Node => Node);
   end Next_Unchecked;

   function Next (Container : Map; Position : Cursor) return Cursor is
   begin
      if Position.Node = 0 then
         return No_Element;
      end if;

      if not Has_Element(Container, Position) then
         raise Constraint_Error
           with "Position has no element";
      end if;

      pragma Assert (Vet (Container, Position), "bad cursor in function Next");

      return Next_Unchecked(Container, Position);
   end Next;

   procedure Next (Container : Map; Position : in out Cursor) is
   begin
      Position := Next (Container, Position);
   end Next;

   -------------------
   -- Query_Element --
   -------------------

   procedure Query_Element
     (Container : in out Map;
      Position : Cursor;
      Process  : not null access
                   procedure (Key : Key_Type; Element : Element_Type))
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

      pragma Assert (Vet (Container, Position), "bad cursor in Query_Element");

      declare
         HT : Hash_Table_Type renames Container.HT.all;
         N  : Node_Type renames HT.Nodes (Position.Node);

         B : Natural renames HT.Busy;
         L : Natural renames HT.Lock;

      begin
         B := B + 1;
         L := L + 1;

         declare
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

   -- TODO

   ----------
   -- Read --
   ----------

   procedure Read
     (Stream    : not null access Root_Stream_Type'Class;
      Container : out Map)
   is
      procedure Initialize_Node (N : in out Node_Type);
      pragma Inline (Initialize_Node);

      procedure Allocate_Node is
         new HT_Ops.Generic_Allocate_Node (Initialize_Node);

      procedure Read is
         new HT_Ops.Generic_Read (Allocate_Node);

      ---------------------
      -- Initialize_Node --
      ---------------------

      procedure Initialize_Node (N : in out Node_Type) is
      begin
         Key_Type'Read (Stream, N.Key);
         Element_Type'Read (Stream, N.Element);
      end Initialize_Node;

   --  Start of processing for Read

   begin
      Container.HT := null;
      Read (Stream, Container.HT.all);
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
      Node : constant Node_Access := Key_Ops.Find (Container.HT.all, Key);

   begin
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if Node = 0 then
         raise Constraint_Error with
           "attempt to replace key not in map";
      end if;

      if Container.HT.Lock > 0 then
         raise Program_Error with
           "Replace attempted to tamper with cursors (map is locked)";
      end if;

      declare
         N : Node_Type renames Container.HT.Nodes (Node);
      begin
         N.Key := Key;
         N.Element := New_Item;
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

      if Container.HT.Lock > 0 then
         raise Program_Error with
           "Replace_Element attempted to tamper with cursors (map is locked)";
      end if;

      pragma Assert (Vet (Container, Position), "bad cursor in Replace_Element");

      Container.HT.Nodes (Position.Node).Element := New_Item;
   end Replace_Element;

   ----------------------
   -- Reserve_Capacity --
   ----------------------

   procedure Reserve_Capacity
     (Container : in out Map;
      Capacity  : Count_Type)
   is
   begin
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      HT_Ops.Reserve_Capacity (Container.HT.all, Capacity);
   end Reserve_Capacity;

   -----------
   -- Right --
   -----------

   function Right (Container : Map; Position : Cursor) return Map is
      Last : Count_Type;
      Lst : Count_Type;
      L : Count_Type := 0;
      C : Count_Type := Position.Node;
   begin

      if C = 0 then
         return (Capacity => Container.Capacity,
                 Modulus => Container.Modulus,
                 K => Part,
                 HT => Container.HT,
                 Length => 0,
                 First => 0,
                 Last => 0);
      end if;

      if Container.K = Plain then
         Lst := 0;
      else
         Lst := HT_Ops.Next(Container.HT.all, Container.Last);
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
         Last := C;
         C := HT_Ops.Next(Container.HT.all, C);
         L := L + 1;
      end loop;

      return (Capacity => Container.Capacity,
              Modulus => Container.Modulus,
              K => Part,
              HT => Container.HT,
              Length => L,
              First => Position.Node,
              Last => Last);
   end Right;


   ---------------------
   -- Set_Has_Element --
   ---------------------

   procedure Set_Has_Element
     (HT   : in out Hash_Table_Type;
      Node : Node_Access;
      Has_Element : Boolean)
   is
   begin
      HT.Nodes (Node).Has_Element := Has_Element;
   end Set_Has_Element;

   --------------
   -- Set_Next --
   --------------

   procedure Set_Next
     (HT   : in out Hash_Table_Type;
      Node : Node_Access;
      Next : Node_Access)
   is
   begin
      HT.Nodes (Node).Next := Next;
   end Set_Next;

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

      pragma Assert (Vet (Container, Position), "bad cursor in Update_Element");

      declare
         HT : Hash_Table_Type renames Container.HT.all;
         B  : Natural renames HT.Busy;
         L  : Natural renames HT.Lock;

      begin
         B := B + 1;
         L := L + 1;

         declare
            N : Node_Type renames HT.Nodes (Position.Node);
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

   ---------
   -- Vet --
   ---------

   function Vet (Container : Map; Position : Cursor) return Boolean is
   begin
      if Position.Node = 0 then
         return true;
      end if;

      return HT_Ops.Vet (Container.HT.all, Position.Node);
   end Vet;

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

      procedure Write_Nodes is new HT_Ops.Generic_Write (Write_Node);

      ----------------
      -- Write_Node --
      ----------------

      procedure Write_Node
        (Stream : not null access Root_Stream_Type'Class;
         Node   : Node_Access)
      is
         N : Node_Type renames Container.HT.Nodes (Node);

      begin
         Key_Type'Write (Stream, N.Key);
         Element_Type'Write (Stream, N.Element);
      end Write_Node;

   --  Start of processing for Write

   begin
      Write_Nodes (Stream, Container.HT.all);
   end Write;

   procedure Write
     (Stream : not null access Root_Stream_Type'Class;
      Item   : Cursor)
   is
   begin
      raise Program_Error with "attempt to stream map cursor";
   end Write;

end Verified_Hashed_Maps;
