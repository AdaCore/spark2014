------------------------------------------------------------------------------
--                                                                          --
--                         GNAT LIBRARY COMPONENTS                          --
--                                                                          --
--   A D A . C O N T A I N E R S . B O U N D E D _ H A S H E D _ S E T S    --
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
-- This unit has originally being developed by Matthew J Heaney.            --
------------------------------------------------------------------------------

with Ada.Text_IO;

with Ada.Containers;
use Ada.Containers;

with Verified_Hash_Tables.Generic_Operations;
pragma Elaborate_All (Verified_Hash_Tables.Generic_Operations);

with Verified_Hash_Tables.Generic_Keys;
pragma Elaborate_All (Verified_Hash_Tables.Generic_Keys);

with System; use type System.Address;

package body Verified_Hashed_Sets is

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Difference
     (Left, Right : Set;
      Target      : in out Hash_Table_Type);

   function Equivalent_Keys
     (Key  : Element_Type;
      HT   : Hash_Table_Type;
      Node : Node_Access) return Boolean;
   pragma Inline (Equivalent_Keys);

   function Get_Next
     (HT   : Hash_Table_Type;
      Node : Node_Access) return Node_Access;
   pragma Inline (Get_Next);

   function Hash_Node
     (HT   : Hash_Table_Type;
      Node : Node_Access) return Hash_Type;
   pragma Inline (Hash_Node);

   procedure Intersection
     (Left : Hash_Table_Type;
      Right : Set;
      Target      : in out Hash_Table_Type);

   procedure Insert
     (HT       : in out Hash_Table_Type;
      New_Item : Element_Type;
      Node     : out Node_Access;
      Inserted : out Boolean);

   function Next_Unchecked
     (Container : Set;
      Position : Cursor) return Cursor;

   procedure Replace_Element
     (HT   : in out Hash_Table_Type;
      Node : Node_Access;
      Key  : Element_Type);

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

   function Vet (Container : Set; Position : Cursor) return Boolean;

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

   package Element_Keys is
     new Verified_Hash_Tables.Generic_Keys
       (HT_Types  => HT_Types,
        Get_Next  => Get_Next,
        Set_Next  => Set_Next,
        Key_Type  => Element_Type,
        Hash      => Hash,
        Equivalent_Keys => Equivalent_Keys);

   ---------
   -- "=" --
   ---------

   function "=" (Left, Right : Set) return Boolean is
      CuL : Cursor := First(Left);
      CuR : Cursor := First(Right);
   begin
      if Length(Left) /= Length(Right) then
         return false;
      end if;

      while CuL.Node /= 0 or CuR.Node /= 0 loop
         if CuL.Node /= CuR.Node or else
           Left.HT.Nodes(CuL.Node).Element /= Right.HT.Nodes(CuR.Node).Element then
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

   procedure Assign (Target : in out Set; Source : Set) is
      procedure Process (Src_Node : Node_Access);

      procedure Iterate is
        new HT_Ops.Generic_Iteration (Process);

      -------------
      -- Process --
      -------------

      procedure Process (Src_Node : Node_Access) is
         X : Node_Access;
         B : Boolean;
      begin
         Insert (Target.HT.all, Source.HT.Nodes (Src_Node).Element, X, B);  -- ???
         pragma Assert (B);
      end Process;

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
         raise Storage_Error with "not enough capacity";  -- SE or CE? ???
      end if;

      Target.Clear;

      case Source.K is
         when Plain =>
            Iterate (Source.HT.all);
         when Part =>
            declare
               N : Count_Type := Source.First;
            begin
               while N /= HT_Ops.Next(Source.HT.all, Source.Last) loop
                  process(N);
                  N := HT_Ops.Next(Source.HT.all, N);
               end loop;
            end;
      end case;
   end Assign;

   --------------
   -- Capacity --
   --------------

   function Capacity (Container : Set) return Count_Type is
   begin
      return Container.HT.Nodes'Length;
   end Capacity;

   -----------
   -- Clear --
   -----------

   procedure Clear (Container : in out Set) is
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
      C : constant Count_Type := Count_Type'Max (Capacity, Source.Capacity);
      H : Hash_Type := 1;
      N : Count_Type := 1;
      Target : Set(C, Source.Modulus);
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

   procedure Delete
     (Container : in out Set;
      Item      : Element_Type)
   is
      X : Node_Access;

   begin

      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      Element_Keys.Delete_Key_Sans_Free (Container.HT.all, Item, X);

      if X = 0 then
         raise Constraint_Error with "attempt to delete element not in set";
      end if;
      HT_Ops.Free (Container.HT.all, X);
   end Delete;

   procedure Delete
     (Container : in out Set;
      Position  : in out Cursor)
   is
   begin

      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if not Has_Element(Container, Position) then
         raise Constraint_Error with "Position cursor has no element";
      end if;

      if Container.HT.Busy > 0 then
         raise Program_Error with
           "attempt to tamper with elements (set is busy)";
      end if;

      pragma Assert (Vet (Container, Position), "bad cursor in Delete");

      HT_Ops.Delete_Node_Sans_Free (Container.HT.all, Position.Node);
      HT_Ops.Free (Container.HT.all, Position.Node);
   end Delete;

   ----------------
   -- Difference --
   ----------------

   procedure Difference
     (Target : in out Set;
      Source : Set)
   is
      Tgt_Node, Src_Node, Src_Last, Src_Length : Node_Access;

      TN : Nodes_Type renames Target.HT.Nodes;
      SN : Nodes_Type renames Source.HT.Nodes;

   begin

      if Target.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if Target'Address = Source'Address then
         Clear (Target);
         return;
      end if;

      case Source.K is
         when Plain =>
            Src_Length := Source.HT.Length;
         when Part=>
            Src_Length := Source.Length;
      end case;

      if Src_Length = 0 then
         return;
      end if;

      if Target.HT.Busy > 0 then
         raise Program_Error with
           "attempt to tamper with elements (set is busy)";
      end if;

      case Source.K is
         when Plain =>
            if Src_Length >= Target.HT.Length then
               Tgt_Node := HT_Ops.First (Target.HT.all);
               while Tgt_Node /= 0 loop
                  if Element_Keys.Find (Source.HT.all, TN (Tgt_Node).Element) /= 0 then
                     declare
                        X : Node_Access := Tgt_Node;
                     begin
                        Tgt_Node := HT_Ops.Next (Target.HT.all, Tgt_Node);
                        HT_Ops.Delete_Node_Sans_Free (Target.HT.all, X);
                        HT_Ops.Free (Target.HT.all, X);
                     end;
                  else
                     Tgt_Node := HT_Ops.Next (Target.HT.all, Tgt_Node);
                  end if;
               end loop;
               return;
            else
               Src_Node := HT_Ops.First (Source.HT.all);
               Src_Last := 0;
            end if;
         when Part=>
            Src_Node := Source.First;
            Src_Last := HT_Ops.Next (Source.HT.all, Source.Last);
      end case;
      while Src_Node /= Src_Last loop
         Tgt_Node := Element_Keys.Find
           (Target.HT.all, SN (Src_Node).Element);

         if Tgt_Node /= 0 then
            HT_Ops.Delete_Node_Sans_Free (Target.HT.all, Tgt_Node);
            HT_Ops.Free (Target.HT.all, Tgt_Node);
         end if;

         Src_Node := HT_Ops.Next (Source.HT.all, Src_Node);
      end loop;
   end Difference;

   procedure Difference
     (Left, Right : Set;
      Target      : in out Hash_Table_Type)
   is
      procedure Process (L_Node : Node_Access);

      procedure Iterate is
        new HT_Ops.Generic_Iteration (Process);

      -------------
      -- Process --
      -------------

      procedure Process (L_Node : Node_Access) is
         E : Element_Type renames Left.HT.Nodes (L_Node).Element;
         X : Node_Access;
         B : Boolean;

      begin
         if Find (Right, E).Node = 0 then
            Insert (Target, E, X, B);
            pragma Assert (B);
         end if;
      end Process;

      --  Start of processing for Difference

   begin
      if Left.K = Plain then
         Iterate (Left.HT.all);
      else

         if Left.Length = 0 then
            return;
         end if;

         declare
            Node : Count_Type := Left.First;
         begin
            while Node /= Left.HT.Nodes(Left.Last).Next loop
               Process(Node);
               Node := HT_Ops.Next(Left.HT.all, Node);
            end loop;
         end;
      end if;
   end Difference;

   function Difference (Left, Right : Set) return Set is
      C : Count_Type;
      H : Hash_Type;
      S : Set (C, H);
   begin
      if Left'Address = Right'Address then
         return Empty_Set;
      end if;

      if Length(Left) = 0 then
         return Empty_Set;
      end if;

      if Length(Right) = 0 then
         return Left.Copy;
      end if;

      C := Length(Left);
      H := Default_Modulus (C);
      Difference (Left, Right, Target => S.HT.all);
      return S;
   end Difference;

   -------------
   -- Element --
   -------------

   function Element (Container : Set; Position : Cursor) return Element_Type is
   begin
      if not Has_Element(Container, Position) then
         raise Constraint_Error with "Position cursor equals No_Element";
      end if;

      pragma Assert (Vet (Container, Position), "bad cursor in function Element");

      declare
         HT : Hash_Table_Type renames Container.HT.all;
      begin
         return HT.Nodes (Position.Node).Element;
      end;
   end Element;

   ---------------------
   -- Equivalent_Sets --
   ---------------------

   function Equivalent_Sets (Left, Right : Set) return Boolean is
   begin
      if Left.K = Plain and Right.K = Plain then
         declare

            function Find_Equivalent_Key
              (R_HT   : Hash_Table_Type;
               L_Node : Node_Access) return Boolean;

            function Is_Equivalent is
              new HT_Ops.Generic_Equal (Find_Equivalent_Key);

            -------------------------
            -- Find_Equivalent_Key --
            -------------------------

            function Find_Equivalent_Key
              (R_HT   : Hash_Table_Type;
               L_Node : Node_Access) return Boolean
            is
               LN  : Node_Type renames Left.HT.Nodes (L_Node);
               RNN : Nodes_Type renames R_HT.Nodes;

               R_Index : constant Hash_Type :=
                 Element_Keys.Index (R_HT, LN.Element);

               R_Node  : Node_Access := R_HT.Buckets (R_Index);

            begin
               loop
                  if R_Node = 0 then
                     return False;
                  end if;

                  if Equivalent_Elements (LN.Element, RNN (R_Node).Element) then
                     return True;
                  end if;

                  R_Node := Get_Next (R_HT, R_Node);
               end loop;
            end Find_Equivalent_Key;

            --  Start of processing of Equivalent_Sets

         begin
            return Is_Equivalent (Left.HT.all, Right.HT.all);
         end;
      else
         declare

            -- To and From are valid and Length are equal
            function Equal_Between
              (L : Hash_Table_Type; R : Set;
               From : Count_Type; To : Count_Type) return Boolean
            is
               L_Index : Hash_Type;
               To_Index : Hash_Type := Element_Keys.Index (L, L.Nodes(To).Element);
               L_Node  : Node_Access := From;

            begin

               L_Index := Element_Keys.Index (L, L.Nodes(From).Element);

               --  For each node of hash table L, search for an equivalent node in hash
               --  table R.

               while L_Index /= To_Index or else L_Node /= HT_Ops.Next(L, To) loop
                  pragma Assert (L_Node /= 0);

                  if Find (R, L.Nodes(L_Node).Element).Node = 0 then
                     return False;
                  end if;

                  L_Node := L.Nodes(L_Node).Next;

                  if L_Node = 0 then
                     --  We have exhausted the nodes in this bucket
                     --  Find the next bucket

                     loop
                        L_Index := L_Index + 1;
                        L_Node := L.Buckets (L_Index);
                        exit when L_Node /= 0;
                     end loop;
                  end if;
               end loop;

               return true;
            end Equal_Between;

         begin
            if Length(Left) /= Length(Right) then
               return False;
            end if;
            if Length(Left) = 0 then
               return True;
            end if;
            if Left.K = Part then
               return Equal_Between(Left.HT.all, Right, Left.First, Left.Last);
            else
               return Equal_Between(Right.HT.all, Left, Right.First, Right.Last);
            end if;
         end;
      end if;
   end Equivalent_Sets;

   -------------------------
   -- Equivalent_Elements --
   -------------------------

   function Equivalent_Elements (Left : Set; CLeft : Cursor;
                                 Right : Set; CRight : Cursor)
                                 return Boolean is
   begin
      if not Has_Element(Left, CLeft) then
         raise Constraint_Error with
           "Left cursor of Equivalent_Elements has no element";
      end if;

      if not Has_Element(Right, CRight) then
         raise Constraint_Error with
           "Right cursor of Equivalent_Elements has no element";
      end if;

      pragma Assert (Vet (Left, CLeft), "bad Left cursor in Equivalent_Elements");
      pragma Assert (Vet (Right, CRight), "bad Right cursor in Equivalent_Elements");

      declare
         LN : Node_Type renames Left.HT.Nodes (CLeft.Node);
         RN : Node_Type renames Right.HT.Nodes (CRight.Node);
      begin
         return Equivalent_Elements (LN.Element, RN.Element);
      end;
   end Equivalent_Elements;

   function Equivalent_Elements (Left : Set; CLeft : Cursor; Right : Element_Type)
                                 return Boolean is
   begin
      if not Has_Element(Left, CLeft) then
         raise Constraint_Error with
           "Left cursor of Equivalent_Elements has no element";
      end if;

      pragma Assert (Vet (Left, CLeft), "Left cursor in Equivalent_Elements is bad");

      declare
         LN : Node_Type renames Left.HT.Nodes (CLeft.Node);
      begin
         return Equivalent_Elements (LN.Element, Right);
      end;
   end Equivalent_Elements;

   function Equivalent_Elements (Left : Element_Type; Right : Set; CRight : Cursor)
                                 return Boolean is
   begin
      if not Has_Element(Right, CRight) then
         raise Constraint_Error with
           "Right cursor of Equivalent_Elements has no element";
      end if;

      pragma Assert
        (Vet (Right, CRight),
         "Right cursor of Equivalent_Elements is bad");

      declare
         RN : Node_Type renames Right.HT.Nodes (CRight.Node);
      begin
         return Equivalent_Elements (Left, RN.Element);
      end;
   end Equivalent_Elements;

   -- NOT MODIFIED

   ---------------------
   -- Equivalent_Keys --
   ---------------------

   function Equivalent_Keys
     (Key  : Element_Type;
      HT   : Hash_Table_Type;
      Node : Node_Access) return Boolean
   is
      N : Node_Type renames HT.Nodes (Node);
   begin
      return Equivalent_Elements (Key, N.Element);
   end Equivalent_Keys;

   -------------
   -- Exclude --
   -------------

   procedure Exclude
     (Container : in out Set;
      Item      : Element_Type)
   is
      X : Node_Access;
   begin
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;
      Element_Keys.Delete_Key_Sans_Free (Container.HT.all, Item, X);
      HT_Ops.Free (Container.HT.all, X);
   end Exclude;

   ----------
   -- Find --
   ----------

   function Find
     (Container : Set;
      Item      : Element_Type) return Cursor
   is
   begin
      case Container.K is
         when Plain =>
            declare
               Node : constant Node_Access := Element_Keys.Find (Container.HT.all, Item);

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
                  Key : Element_Type;
                  From : Count_Type;
                  To : Count_Type) return Node_Access is

                  Indx : Hash_Type;
                  Indx_From : Hash_Type := Element_Keys.Index (HT, HT.Nodes(From).Element);
                  Indx_To : Hash_Type := Element_Keys.Index (HT, HT.Nodes(To).Element);
                  Node : Node_Access;
                  To_Node : Node_Access;

               begin

                  Indx := Element_Keys.Index (HT, Key);

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
                     if Equivalent_Keys (Key, HT, Node) then
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

               return (Node => Find_Between(Container.HT.all, Item,
                       Container.First, Container.Last));
            end;
      end case;
   end Find;

   -----------
   -- First --
   -----------

   function First (Container : Set) return Cursor is
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

   -- NOT MODIFIED

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

   function Has_Element (Container : Set; Position : Cursor) return Boolean is
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
           Element_Keys.Index(Container.HT.all,
                              Container.HT.Nodes(Container.Last).Element);
         Fst_Index : Hash_Type :=
           Element_Keys.Index(Container.HT.all,
                              Container.HT.Nodes(Container.First).Element);
         Index : Hash_Type :=
           Element_Keys.Index(Container.HT.all,
                              Container.HT.Nodes(Position.Node).Element);
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
      return Hash (HT.Nodes (Node).Element);
   end Hash_Node;

   -------------
   -- Include --
   -------------

   procedure Include
     (Container : in out Set;
      New_Item  : Element_Type)
   is
      Position : Cursor;
      Inserted : Boolean;

   begin
      Insert (Container, New_Item, Position, Inserted);

      if not Inserted then
         if Container.HT.Lock > 0 then
            raise Program_Error with
              "attempt to tamper with cursors (set is locked)";
         end if;

         Container.HT.Nodes (Position.Node).Element := New_Item;
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
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      Insert (Container.HT.all, New_Item, Position.Node, Inserted);
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

   procedure Insert
     (HT       : in out Hash_Table_Type;
      New_Item : Element_Type;
      Node     : out Node_Access;
      Inserted : out Boolean)
   is
      function New_Node (Next : Node_Access) return Node_Access;
      pragma Inline (New_Node);

      procedure Local_Insert is
        new Element_Keys.Generic_Conditional_Insert (New_Node);

      procedure Initialize_Node (Node : in out Node_Type);
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

      procedure Initialize_Node (Node : in out Node_Type) is
      begin
         Node.Element := New_Item;
         Node.Has_Element := True;
      end Initialize_Node;

      --  Start of processing for Insert

   begin
      Local_Insert (HT, New_Item, Node, Inserted);
   end Insert;

   ------------------
   -- Intersection --
   ------------------

   procedure Intersection
     (Target : in out Set;
      Source : Set)
   is
      Tgt_Node : Node_Access;
      TN       : Nodes_Type renames Target.HT.Nodes;

   begin
      if Target.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if Target'Address = Source'Address then
         return;
      end if;

      if Source.HT.Length = 0 then
         Clear (Target);
         return;
      end if;

      if Target.HT.Busy > 0 then
         raise Program_Error with
           "attempt to tamper with elements (set is busy)";
      end if;

      Tgt_Node := HT_Ops.First (Target.HT.all);
      while Tgt_Node /= 0 loop
         if Find (Source, TN (Tgt_Node).Element).Node /= 0 then
            Tgt_Node := HT_Ops.Next (Target.HT.all, Tgt_Node);

         else
            declare
               X : Node_Access := Tgt_Node;
            begin
               Tgt_Node := HT_Ops.Next (Target.HT.all, Tgt_Node);
               HT_Ops.Delete_Node_Sans_Free (Target.HT.all, X);
               HT_Ops.Free (Target.HT.all, X);
            end;
         end if;
      end loop;
   end Intersection;

   procedure Intersection
     (Left : Hash_Table_Type;
      Right : Set;
      Target : in out Hash_Table_Type)
   is
      procedure Process (L_Node : Node_Access);

      procedure Iterate is
        new HT_Ops.Generic_Iteration (Process);

      -------------
      -- Process --
      -------------

      procedure Process (L_Node : Node_Access) is
         E : Element_Type renames Left.Nodes (L_Node).Element;
         X : Node_Access;
         B : Boolean;

      begin
         if Find (Right, E).Node /= 0 then
            Insert (Target, E, X, B);
            pragma Assert (B);
         end if;
      end Process;

      --  Start of processing for Intersection

   begin
      Iterate (Left);
   end Intersection;

   function Intersection (Left, Right : Set) return Set is
      C : Count_Type;
      H : Hash_Type;
      X : Node_Access;
      B : Boolean;

   begin
      if Left'Address = Right'Address then
         return Left.Copy;
      end if;

      C := Count_Type'Min (Length(Left), Length(Right));  -- ???
      H := Default_Modulus (C);
      return S : Set (C, H) do
         if Length(Left) /= 0 and Length(Right) /= 0 then
            if Left.K = Plain then
               Intersection (Left.HT.all, Right, Target => S.HT.all);
            else
               C := Left.First;
               while C /= Left.HT.Nodes(Left.Last).Next loop
                  pragma Assert (C /= 0);
                  if Find (Right, Left.HT.Nodes(C).Element).Node /= 0 then
                     Insert (S.HT.all, Left.HT.Nodes(C).Element, X, B);
                     pragma Assert (B);
                  end if;
                  C := Left.HT.Nodes(C).Next;
               end loop;
            end if;
         end if;
      end return;
   end Intersection;

   --------------
   -- Is_Empty --
   --------------

   function Is_Empty (Container : Set) return Boolean is
   begin
      return Length(Container) = 0;
   end Is_Empty;

   ---------------
   -- Is_Subset --
   ---------------

   function Is_Subset (Subset : Set; Of_Set : Set) return Boolean is
      Subset_Node  : Node_Access;
      Subset_Nodes : Nodes_Type renames Subset.HT.Nodes;
      To_Node : Count_Type;
   begin
      if Subset'Address = Of_Set'Address then
         return True;
      end if;

      if Length(Subset) > Length(Of_Set) then
         return False;
      end if;

      Subset_Node := First (Subset).Node;

      if Subset.K = Plain then
         To_Node := 0;
      else
         To_Node := Subset.HT.Nodes(Subset.Last).Next;
      end if;

      while Subset_Node /= To_Node loop
         declare
            N : Node_Type renames Subset_Nodes (Subset_Node);
            E : Element_Type renames N.Element;

         begin
            if Find (Of_Set, E).Node = 0 then
               return False;
            end if;
         end;

         Subset_Node := HT_Ops.Next (Subset.HT.all, Subset_Node);
      end loop;

      return True;
   end Is_Subset;

   -------------
   -- Iterate --
   -------------

   procedure Iterate
     (Container : Set;
      Process   : not null access procedure (Container : Set; Position : Cursor))
   is
      procedure Process_Node (Node : Node_Access);
      pragma Inline (Process_Node);

      procedure Iterate is
        new HT_Ops.Generic_Iteration (Process_Node);

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
               Iterate (Container.HT.all);
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

   ----------
   -- Left --
   ----------

   function Left (Container : Set; Position : Cursor) return Set is
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

   function Length (Container : Set) return Count_Type is
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

   procedure Move (Target : in out Set; Source : in out Set) is
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
         Insert (Target, NN (X).Element);  -- optimize???

         Y := HT_Ops.Next (HT, X);

         HT_Ops.Delete_Node_Sans_Free (HT, X);
         HT_Ops.Free (HT, X);

         X := Y;
      end loop;
   end Move;

   ----------
   -- Next --
   ----------

   function Next_Unchecked (Container : Set; Position : Cursor) return Cursor is
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

   function Next (Container : Set; Position : Cursor) return Cursor is
   begin
      if Position.Node = 0 then
         return No_Element;
      end if;

      if not Has_Element(Container, Position) then
         raise Constraint_Error
           with "Position has no element";
      end if;

      pragma Assert (Vet (Container, Position), "bad cursor in Next");

      return Next_Unchecked(Container, Position);
   end Next;

   procedure Next (Container : Set; Position : in out Cursor) is
   begin
      Position := Next (Container, Position);
   end Next;

   -------------
   -- Overlap --
   -------------

   function Overlap (Left, Right : Set) return Boolean is
      Left_Node  : Node_Access;
      Left_Nodes : Nodes_Type renames Left.HT.Nodes;
      To_Node : Node_Access;
   begin
      if Length(Right) = 0 or Length(Left) = 0 then
         return False;
      end if;

      if Left'Address = Right'Address then
         return True;
      end if;

      Left_Node := First (Left).Node;

      if Left.K = Plain then
         To_Node := 0;
      else
         To_Node := Left.HT.Nodes(Left.Last).Next;
      end if;

      while Left_Node /= To_Node loop
         declare
            N : Node_Type renames Left_Nodes (Left_Node);
            E : Element_Type renames N.Element;

         begin
            if Find (Right, E).Node /= 0 then
               return True;
            end if;
         end;

         Left_Node := HT_Ops.Next (Left.HT.all, Left_Node);
      end loop;

      return False;
   end Overlap;

   -------------------
   -- Query_Element --
   -------------------

   procedure Query_Element
     (Container : in out Set;
      Position : Cursor;
      Process  : not null access procedure (Element : Element_Type))
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

         B : Natural renames HT.Busy;
         L : Natural renames HT.Lock;

      begin
         B := B + 1;
         L := L + 1;

         begin
            Process (HT.Nodes (Position.Node).Element);
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

   -- TODO !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

   procedure Read
     (Stream    : not null access Root_Stream_Type'Class;
      Container : out Set)
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
         Element_Type'Read (Stream, N.Element);
      end Initialize_Node;

      --  Start of processing for Read

      C : Set(0,0);
   begin
      Container := C;
      Read (Stream, Container.HT.all);
   end Read;

   procedure Read
     (Stream : not null access Root_Stream_Type'Class;
      Item   : out Cursor)
   is
   begin
      raise Program_Error with "attempt to stream set cursor";
   end Read;

   -------------
   -- Replace --
   -------------

   procedure Replace
     (Container : in out Set;
      New_Item  : Element_Type)
   is
      Node : constant Node_Access :=
        Element_Keys.Find (Container.HT.all, New_Item);

   begin
      if Container.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if Node = 0 then
         raise Constraint_Error with
           "attempt to replace element not in set";
      end if;

      if Container.HT.Lock > 0 then
         raise Program_Error with
           "attempt to tamper with cursors (set is locked)";
      end if;

      Container.HT.Nodes (Node).Element := New_Item;
   end Replace;

   ---------------------
   -- Replace_Element --
   ---------------------

   procedure Replace_Element
     (HT   : in out Hash_Table_Type;
      Node : Node_Access;
      Key  : Element_Type)
   is
      function Hash_Node (Node : Node_Access) return Hash_Type;
      pragma Inline (Hash_Node);

      procedure Assign (Node : Node_Access; Item : Element_Type);
      pragma Inline (Assign);

      procedure Local_Replace_Element is
        new Element_Keys.Generic_Replace_Element (Hash_Node, Assign);

      ---------------
      -- Hash_Node --
      ---------------

      function Hash_Node (Node : Node_Access) return Hash_Type is
      begin
         return Hash (HT.Nodes (Node).Element);
      end Hash_Node;

      ------------
      -- Assign --
      ------------

      procedure Assign (Node : Node_Access; Item : Element_Type) is
      begin
         HT.Nodes (Node).Element := Item;
      end Assign;

      --  Start of processing for Replace_Element

   begin
      Local_Replace_Element (HT, Node, Key);
   end Replace_Element;

   procedure Replace_Element
     (Container : in out Set;
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
           "Position cursor has no element";
      end if;

      pragma Assert (Vet (Container, Position), "bad cursor in Replace_Element");

      Replace_Element (Container.HT.all, Position.Node, New_Item);
   end Replace_Element;

   ----------------------
   -- Reserve_Capacity --
   ----------------------

   procedure Reserve_Capacity
     (Container : in out Set;
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

   function Right (Container : Set; Position : Cursor) return Set is
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

   --------------------------
   -- Symmetric_Difference --
   --------------------------

   procedure Symmetric_Difference
     (Target : in out Set;
      Source : Set)
   is
      procedure Process (Src_Node : Node_Access);

      procedure Symmetric_Difference is
        new HT_Ops.Generic_Iteration (Process);

      function New_Node
        (Item : Element_Type;
         Next : Node_Access) return Node_Access;

      -------------
      -- Process --
      -------------

      procedure Process (Src_Node : Node_Access) is
         SN : Node_Type renames Source.HT.Nodes (Src_Node);
         E  : Element_Type renames SN.Element;

         TN : Nodes_Type renames Target.HT.Nodes;
         B  : Buckets_Type renames Target.HT.Buckets;

         J : constant Hash_Type := B'First + Hash (E) mod B'Length;
         L : Count_Type renames Target.HT.Length;

      begin
         if B (J) = 0 then
            B (J) := New_Node (E, 0);
            L := L + 1;

         elsif Equivalent_Elements (E, TN (B (J)).Element) then
            declare
               X : Node_Access := B (J);
            begin
               B (J) := TN (X).Next;
               L := L - 1;
               HT_Ops.Free (Target.HT.all, X);
            end;

         else
            declare
               Prev : Node_Access := B (J);
               Curr : Node_Access := TN (Prev).Next;

            begin
               while Curr /= 0 loop
                  if Equivalent_Elements (E, TN (Curr).Element) then
                     TN (Prev).Next := TN (Curr).Next;
                     L := L - 1;
                     HT_Ops.Free (Target.HT.all, Curr);
                     return;
                  end if;

                  Prev := Curr;
                  Curr := TN (Prev).Next;
               end loop;

               B (J) := New_Node (E, B (J));
               L := L + 1;
            end;
         end if;
      end Process;

      --------------
      -- New_Node --
      --------------

      function New_Node
        (Item : Element_Type;
         Next : Node_Access) return Node_Access
      is
         procedure Initialize_Node (N : in out Node_Type);
         pragma Inline (Initialize_Node);

         procedure Allocate_Node is
           new HT_Ops.Generic_Allocate_Node (Initialize_Node);

         ---------------------
         -- Initialize_Node --
         ---------------------

         procedure Initialize_Node (N : in out Node_Type) is
         begin
            N.Element := Item;
         end Initialize_Node;

         X : Node_Access;

         --  Start of processing for New_Node

      begin
         Allocate_Node (Target.HT.all, X);
         Target.HT.Nodes (X).Next := Next;
         return X;
      end New_Node;

      --  Start of processing for Symmetric_Difference

   begin
      if Target.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if Target'Address = Source'Address then
         Clear (Target);
         return;
      end if;

      if Length(Target) = 0 then
         Assign (Target, Source);
         return;
      end if;

      if Target.HT.Busy > 0 then
         raise Program_Error with
           "attempt to tamper with elements (set is busy)";
      end if;

      if Source.K = Plain then
         Symmetric_Difference (Source.HT.all);
      else

         if Source.Length = 0 then
            return;
         end if;

         declare
            Node : Count_Type := Source.First;
         begin
            while Node /= Source.HT.Nodes(Source.Last).Next loop
               Process (Node);
               Node := HT_Ops.Next(Source.HT.all, Node);
            end loop;
         end;
      end if;

   end Symmetric_Difference;

   function Symmetric_Difference (Left, Right : Set) return Set is
      C : Count_Type;
      H : Hash_Type;

   begin
      if Left'Address = Right'Address then
         return Empty_Set;
      end if;

      if Length(Right) = 0 then
         return Left.Copy;
      end if;

      if Length(Left) = 0 then
         return Right.Copy;
      end if;

      C := Length(Left) + Length(Right);
      H := Default_Modulus (C);
      return S : Set (C, H) do
         Difference (Left, Right, S.HT.all);
         Difference (Right, Left, S.HT.all);
      end return;
   end Symmetric_Difference;

   ------------
   -- To_Set --
   ------------

   function To_Set (New_Item : Element_Type) return Set is
      X : Node_Access;
      B : Boolean;

   begin
      return S : Set (Capacity => 1, Modulus => 1) do
         Insert (S.HT.all, New_Item, X, B);
         pragma Assert (B);
      end return;
   end To_Set;

   -----------
   -- Union --
   -----------

   procedure Union
     (Target : in out Set;
      Source : Set)
   is
      procedure Process (Src_Node : Node_Access);

      procedure Iterate is
        new HT_Ops.Generic_Iteration (Process);

      -------------
      -- Process --
      -------------

      procedure Process (Src_Node : Node_Access) is
         N : Node_Type renames Source.HT.Nodes (Src_Node);
         E : Element_Type renames N.Element;

         X : Node_Access;
         B : Boolean;

      begin
         Insert (Target.HT.all, E, X, B);
      end Process;

      --  Start of processing for Union

   begin

      if Target.K /= Plain then
         raise Constraint_Error
           with "Can't modify part of container";
      end if;

      if Target'Address = Source'Address then
         return;
      end if;

      if Target.HT.Busy > 0 then
         raise Program_Error with
           "attempt to tamper with elements (set is busy)";
      end if;

      if Source.K = Plain then
         Iterate (Source.HT.all);
      else

         if Source.Length = 0 then
            return;
         end if;

         declare
            Node : Count_Type := Source.First;
         begin
            while Node /= Source.HT.Nodes(Source.Last).Next loop
               Process(Node);
               Node := HT_Ops.Next(Source.HT.all, Node);
            end loop;
         end;
      end if;
   end Union;

   function Union (Left, Right : Set) return Set is
      C : Count_Type;
      H : Hash_Type;

   begin
      if Left'Address = Right'Address then
         return Left.Copy;
      end if;

      if Length(Right) = 0 then
         return Left.Copy;
      end if;

      if Length(Left) = 0 then
         return Right.Copy;
      end if;

      C := Length(Left) + Length(Right);
      H := Default_Modulus (C);
      return S : Set (C, H) do
         Assign (Target => S, Source => Left);
         Union (Target => S, Source => Right);
      end return;
   end Union;

   ---------
   -- Vet --
   ---------

   function Vet (Container : Set; Position : Cursor) return Boolean is
   begin
      if Position.Node = 0 then
         return false;
      end if;

      return HT_Ops.Vet (Container.HT.all, Position.Node);
   end Vet;

   -----------
   -- Write --
   -----------

   -- TODO !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

   procedure Write
     (Stream    : not null access Root_Stream_Type'Class;
      Container : Set)
   is
      procedure Write_Node
        (Stream : not null access Root_Stream_Type'Class;
         Node   : Node_Access);
      pragma Inline (Write_Node);

      procedure Write_Nodes is
        new HT_Ops.Generic_Write (Write_Node);

      ----------------
      -- Write_Node --
      ----------------

      procedure Write_Node
        (Stream : not null access Root_Stream_Type'Class;
         Node   : Node_Access)
      is
      begin
         Element_Type'Write (Stream, Container.HT.Nodes (Node).Element);
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
      raise Program_Error with "attempt to stream set cursor";
   end Write;

   package body Generic_Keys is

      -----------------------
      -- Local Subprograms --
      -----------------------

      function Equivalent_Key_Node
        (Key  : Key_Type;
         HT   : Hash_Table_Type;
         Node : Node_Access) return Boolean;
      pragma Inline (Equivalent_Key_Node);

      --------------------------
      -- Local Instantiations --
      --------------------------

      package Key_Keys is
        new Verified_Hash_Tables.Generic_Keys
          (HT_Types  => HT_Types,
           Get_Next  => Get_Next,
           Set_Next  => Set_Next,
           Key_Type  => Key_Type,
           Hash      => Hash,
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

      procedure Delete
        (Container : in out Set;
         Key       : Key_Type)
      is
         X : Node_Access;

      begin
         if Container.K /= Plain then
            raise Constraint_Error
              with "Can't modify part of container";
         end if;

         Key_Keys.Delete_Key_Sans_Free (Container.HT.all, Key, X);

         if X = 0 then
            raise Constraint_Error with "attempt to delete key not in set";
         end if;

         HT_Ops.Free (Container.HT.all, X);
      end Delete;

      -------------
      -- Element --
      -------------

      function Element
        (Container : Set;
         Key       : Key_Type) return Element_Type
      is
         Node : constant Node_Access := Find (Container, Key).Node;

      begin
         if Node = 0 then
            raise Constraint_Error with "key not in map";
         end if;

         return Container.HT.Nodes (Node).Element;
      end Element;

      -------------------------
      -- Equivalent_Key_Node --
      -------------------------

      function Equivalent_Key_Node
        (Key  : Key_Type;
         HT   : Hash_Table_Type;
         Node : Node_Access) return Boolean
      is
         N : Nodes_Type renames HT.Nodes;
         E : Element_Type renames N (Node).Element;
         K : constant Key_Type := Generic_Keys.Key (E);

      begin
         return Equivalent_Keys (Key, K);
      end Equivalent_Key_Node;

      -------------
      -- Exclude --
      -------------

      procedure Exclude
        (Container : in out Set;
         Key       : Key_Type)
      is
         X : Node_Access;
      begin
         if Container.K /= Plain then
            raise Constraint_Error
              with "Can't modify part of container";
         end if;

         Key_Keys.Delete_Key_Sans_Free (Container.HT.all, Key, X);
         HT_Ops.Free (Container.HT.all, X);
      end Exclude;

      ----------
      -- Find --
      ----------




      function Find
        (Container : Set;
         Key       : Key_Type) return Cursor
      is
      begin
         if Container.K = Plain then
            declare
               Node : constant Node_Access :=
                 Key_Keys.Find (Container.HT.all, Key);

            begin
               if Node = 0 then
                  return No_Element;
               end if;

               return (Node => Node);
            end;
         else declare
               function Find_Between
                 (HT  : Hash_Table_Type;
                  Key : Key_Type;
                  From : Count_Type;
                  To : Count_Type) return Node_Access is

                  Indx : Hash_Type;
                  Indx_From : Hash_Type :=
                    Key_Keys.Index (HT, Generic_Keys.Key (HT.Nodes(From).Element));
                  Indx_To : Hash_Type :=
                    Key_Keys.Index (HT, Generic_Keys.Key (HT.Nodes(To).Element));
                  Node : Node_Access;
                  To_Node : Node_Access;

               begin

                  Indx := Key_Keys.Index (HT, Key);

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
         end if;
      end Find;

      ---------
      -- Key --
      ---------

      function Key (Container : Set; Position : Cursor) return Key_Type is
      begin
         if not Has_Element(Container, Position) then
            raise Constraint_Error with
              "Position cursor has no element";
         end if;

         pragma Assert (Vet (Container, Position), "bad cursor in function Key");

         declare
            HT : Hash_Table_Type renames Container.HT.all;
            N  : Node_Type renames HT.Nodes (Position.Node);
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
      begin
         if Container.K /= Plain then
            raise Constraint_Error
              with "Can't modify part of container";
         end if;

         declare
            Node : constant Node_Access :=
              Key_Keys.Find (Container.HT.all, Key);

         begin
            if Node = 0 then
               raise Constraint_Error with
                 "attempt to replace key not in set";
            end if;

            Replace_Element (Container.HT.all, Node, New_Item);
         end;
      end Replace;

      -----------------------------------
      -- Update_Element_Preserving_Key --
      -----------------------------------

      procedure Update_Element_Preserving_Key
        (Container : in out Set;
         Position  : Cursor;
         Process   : not null access
           procedure (Element : in out Element_Type))
      is
         HT   : Hash_Table_Type renames Container.HT.all;
         Indx : Hash_Type;

      begin
         if Container.K /= Plain then
            raise Constraint_Error
              with "Can't modify part of container";
         end if;

         --  needs careful review ???

         if not Has_Element(Container, Position) then
            raise Constraint_Error with
              "Position cursor has no element";
         end if;

         if HT.Capacity = 0
           or else HT.Length = 0
           or else Position.Node not in HT.Nodes'Range
           or else HT.Nodes (Position.Node).Next = Position.Node
         then
            raise Program_Error with "Position cursor is bad (set is empty)";
         end if;

         pragma Assert
           (Vet (Container, Position),
            "bad cursor in Update_Element_Preserving_Key");

         Indx := HT_Ops.Index (HT, Position.Node);
         --  capture this value prior to allowing modification,
         --  to ensure we have correct bucket

         declare
            E : Element_Type renames HT.Nodes (Position.Node).Element;
            K : constant Key_Type := Key (E);

            B : Natural renames HT.Busy;
            L : Natural renames HT.Lock;

         begin
            B := B + 1;
            L := L + 1;

            begin
               Process (E);
            exception
               when others =>
                  L := L - 1;
                  B := B - 1;
                  raise;
            end;

            L := L - 1;
            B := B - 1;

            if Equivalent_Keys (K, Key (E)) then
               pragma Assert (Hash (K) = Hash (E));
               return;
            end if;
         end;

         if HT.Buckets (Indx) = Position.Node then
            HT.Buckets (Indx) := HT.Nodes (Position.Node).Next;

         else
            declare
               Prev : Node_Access := HT.Buckets (Indx);

            begin
               while HT.Nodes (Prev).Next /= Position.Node loop
                  Prev := HT.Nodes (Prev).Next;

                  if Prev = 0 then
                     raise Program_Error with
                       "Position cursor is bad (node not found)";
                  end if;
               end loop;

               HT.Nodes (Prev).Next := HT.Nodes (Position.Node).Next;
            end;
         end if;

         HT.Length := HT.Length - 1;

         declare
            X : Node_Access := Position.Node;

         begin
            HT_Ops.Free (HT, X);
         end;

         raise Program_Error with "key was modified";
      end Update_Element_Preserving_Key;

   end Generic_Keys;

end Verified_Hashed_Sets;
