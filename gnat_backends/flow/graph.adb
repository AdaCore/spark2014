------------------------------------------------------------------------------
--                                                                          --
--                            GNAT2WHY COMPONENTS                           --
--                                                                          --
--                                G R A P H                                 --
--                                                                          --
--                                 B o d y                                  --
--                                                                          --
--                  Copyright (C) 2013, Altran UK Limited                   --
--                                                                          --
-- gnat2why is  free  software;  you can redistribute  it and/or  modify it --
-- under terms of the  GNU General Public License as published  by the Free --
-- Software  Foundation;  either version 3,  or (at your option)  any later --
-- version.  gnat2why is distributed  in the hope that  it will be  useful, --
-- but WITHOUT ANY WARRANTY; without even the implied warranty of  MERCHAN- --
-- TABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public --
-- License for  more details.  You should have  received  a copy of the GNU --
-- General  Public License  distributed with  gnat2why;  see file COPYING3. --
-- If not,  go to  http://www.gnu.org/licenses  for a complete  copy of the --
-- license.                                                                 --
--                                                                          --
------------------------------------------------------------------------------

with Ada.Text_IO;
use Ada.Text_IO;

use type Ada.Containers.Count_Type;

package body Graph
is

   ----------------------------------------------------------------------
   --  Local types
   ----------------------------------------------------------------------

   type Vertex_To_Vertex_T is array (Vertex_Id range <>) of Vertex_Id;

   ----------------------------------------------------------------------
   --  Local operations for local callers
   ----------------------------------------------------------------------

   ----------------------------------------------------------------------
   --  Basic operations
   ----------------------------------------------------------------------

   function Create return T
   is (T'(Vertices => VL.Empty_Vector));

   function Create (G : T'Class) return T
   is
      R : T := Create;
   begin
      for V of G.Vertices loop
         R.Vertices.Append (Vertex'(Key            => V.Key,
                                    In_Neighbours  => VIS.Empty_Set,
                                    Out_Neighbours => EAM.Empty_Map));
      end loop;
      return R;
   end Create;

   ----------------------------------------------------------------------
   --  Vertex operations
   ----------------------------------------------------------------------

   function Get_Vertex (G : T'Class;
                        V : Vertex_Key)
                       return Vertex_Id
   is
   begin
      for I in Valid_Vertex_Id range 1 .. G.Vertices.Last_Index loop
         if Test_Key (G.Vertices (I).Key, V) then
            return I;
         end if;
      end loop;
      return Null_Vertex;
   end Get_Vertex;

   function Get_Key (G : T'Class;
                     V : Vertex_Id)
                    return Vertex_Key
   is (G.Vertices (V).Key);

   procedure Add_Vertex (G : in out T'Class;
                         V :        Vertex_Key)
   is
   begin
      G.Vertices.Append (Vertex'(Key            => V,
                                 In_Neighbours  => VIS.Empty_Set,
                                 Out_Neighbours => EAM.Empty_Map));
   end Add_Vertex;

   procedure Add_Vertex (G  : in out T'Class;
                         V  :        Vertex_Key;
                         Id :    out Vertex_Id)
   is
   begin
      G.Add_Vertex (V);
      Id := G.Vertices.Last_Index;
   end Add_Vertex;

   ----------------------------------------------------------------------
   --  Edge operations
   ----------------------------------------------------------------------

   function Edge_Exists (G        : T'Class;
                         V_1, V_2 : Vertex_Id)
                        return Boolean
   is
   begin
      --  Sanity check the indices.
      pragma Assert (V_1 <= G.Vertices.Last_Index and
                       V_2 <= G.Vertices.Last_Index);

      return G.Vertices (V_1).Out_Neighbours.Contains (V_2);
   end Edge_Exists;

   procedure Add_Edge (G        : in out T'Class;
                       V_1, V_2 :        Vertex_Id)
   is
   begin
      --  Sanity check the indices.
      pragma Assert (V_1 <= G.Vertices.Last_Index and
                       V_2 <= G.Vertices.Last_Index);

      --  Do no work if we already have this edge.
      if G.Edge_Exists (V_1, V_2) then
         return;
      end if;

      --  Add to V_1's out neighbours and edge attribute list.
      G.Vertices (V_1).Out_Neighbours.Include
        (V_2, Edge_Attributes'(Marked => False));

      --  Add to V_2's in neighbours.
      G.Vertices (V_2).In_Neighbours.Include (V_1);
   end Add_Edge;

   procedure Add_Edge (G        : in out T'Class;
                       V_1, V_2 :        Vertex_Key)
   is
   begin
      G.Add_Edge (G.Get_Vertex (V_1), G.Get_Vertex (V_2));
   end Add_Edge;

   procedure Remove_Edge (G        : in out T'Class;
                          V_1, V_2 :        Vertex_Id)
   is
   begin
      --  Sanity check the indices.
      pragma Assert (V_1 <= G.Vertices.Last_Index and
                       V_2 <= G.Vertices.Last_Index);

      if G.Edge_Exists (V_1, V_2) then
         --  Note the use of delete, so we better check if there is an
         --  edge we can delete first.
         G.Vertices (V_1).Out_Neighbours.Delete (V_2);
         G.Vertices (V_2).In_Neighbours.Delete (V_1);
      end if;
   end Remove_Edge;

   procedure Mark_Edge (G        : in out T'Class;
                        V_1, V_2 :        Vertex_Id)
   is
   begin
      --  Sanity check the indices.
      pragma Assert (V_1 <= G.Vertices.Last_Index and
                       V_2 <= G.Vertices.Last_Index);

      --  Mark the edge
      G.Vertices (V_1).Out_Neighbours (V_2).Marked := True;
   end Mark_Edge;

   ----------------------------------------------------------------------
   --  Iterators
   ----------------------------------------------------------------------

   type Iterator is new List_Iterators.Forward_Iterator
      with record
         The_Collection : Vertex_Collection_T;
      end record;

   overriding function First (Object : Iterator) return Cursor;
   overriding function Next (Object   : Iterator;
                             Position : Cursor)
                            return Cursor;

   function First (Object : Iterator)
                  return Cursor
   is
      G : access constant T'Class renames Object.The_Collection.The_Graph;
   begin
      case Object.The_Collection.The_Type is
         when In_Neighbours =>
            return Cursor'(Collection_Type   => In_Neighbours,
                           The_Collection    => Object.The_Collection,
                           VIS_Native_Cursor => G.Vertices
                             (Object.The_Collection.Id).In_Neighbours.First);
         when Out_Neighbours =>
            return Cursor'(Collection_Type   => Out_Neighbours,
                           The_Collection    => Object.The_Collection,
                           EAM_Native_Cursor => G.Vertices
                             (Object.The_Collection.Id).Out_Neighbours.First);
         when All_Vertices =>
            return Cursor'(Collection_Type   => All_Vertices,
                           The_Collection    => Object.The_Collection,
                           VL_Native_Cursor  => G.Vertices.First);
      end case;
   end First;

   function Next (Object   : Iterator;
                  Position : Cursor)
                 return Cursor
   is
      G : access constant T'Class renames Object.The_Collection.The_Graph;
   begin
      case Object.The_Collection.The_Type is
         when In_Neighbours =>
            return Cursor'(Collection_Type   => In_Neighbours,
                           The_Collection    => Object.The_Collection,
                           VIS_Native_Cursor => Next
                             (Position.VIS_Native_Cursor));
         when Out_Neighbours =>
            return Cursor'(Collection_Type   => Out_Neighbours,
                           The_Collection    => Object.The_Collection,
                           EAM_Native_Cursor => Next
                             (Position.EAM_Native_Cursor));
         when All_Vertices =>
            return Cursor'(Collection_Type   => All_Vertices,
                           The_Collection    => Object.The_Collection,
                           VL_Native_Cursor  => Next
                             (Position.VL_Native_Cursor));
      end case;
   end Next;

   function Get_Collection (G        : access constant T'Class;
                            V        : Vertex_Id;
                            The_Type : Vertex_Based_Collection)
                           return Vertex_Collection_T'Class
   is (Vertex_Collection_T'(The_Type  => The_Type,
                            The_Graph => G,
                            Id        => V));

   function Get_Collection (G        : access constant T'Class;
                            The_Type : Graph_Based_Collection)
                           return Vertex_Collection_T'Class
   is (Vertex_Collection_T'(The_Type  => The_Type,
                            The_Graph => G,
                            Id        => Null_Vertex));

   function Has_Element (Pos : Cursor) return Boolean
   is
   begin
      case Pos.Collection_Type is
         when In_Neighbours =>
            return Has_Element (Pos.VIS_Native_Cursor);
         when Out_Neighbours =>
            return Has_Element (Pos.EAM_Native_Cursor);
         when All_Vertices =>
            return Has_Element (Pos.VL_Native_Cursor);
      end case;
   end Has_Element;

   function Iterate (Container : Vertex_Collection_T)
                    return List_Iterators.Forward_Iterator'Class
   is (Iterator'(The_Collection => Container));

   function Get_Current_Vertex_Id (Container : Vertex_Collection_T;
                                   Pos       : Cursor)
                                  return Vertex_Id
   is
   begin
      case Pos.Collection_Type is
         when In_Neighbours =>
            return Element (Pos.VIS_Native_Cursor);
         when Out_Neighbours =>
            return Key (Pos.EAM_Native_Cursor);
         when All_Vertices =>
            return To_Index (Pos.VL_Native_Cursor);
      end case;
   end Get_Current_Vertex_Id;

   ----------------------------------------------------------------------
   --  Visitors
   ----------------------------------------------------------------------

   procedure DFS (G             : T'Class;
                  Start         : Vertex_Id;
                  Include_Start : Boolean;
                  Visitor       : access procedure (V : Vertex_Id))
   is
      type Bit_Field is array
        (Valid_Vertex_Id range 1 .. G.Vertices.Last_Index) of Boolean;

      Will_Visit   : Bit_Field         := Bit_Field'(others => False);
      Stack        : Vertex_Index_List := VIL.Empty_Vector;
      Current_Node : Valid_Vertex_Id;
   begin
      --  Seed the stack with either the start node or all its
      --  neighbours.
      if Include_Start then
         Stack.Append (Start);
         Will_Visit (Start) := True;
      else
         for C in G.Vertices (Start).Out_Neighbours.Iterate loop
            declare
               Out_Node : constant Valid_Vertex_Id := Key (C);
            begin
               if not Will_Visit (Out_Node) then
                  Stack.Append (Out_Node);
                  Will_Visit (Out_Node) := True;
               end if;
            end;
         end loop;
      end if;

      while Stack.Length > 0 loop
         --  Pop from the stack.
         Current_Node := Stack.Last_Element;
         Stack.Delete_Last;

         --  Visit the node.
         Visitor (Current_Node);

         --  Push all out-nodes onto the stack, unless they have
         --  already been flagged to be visited.
         for C in G.Vertices (Current_Node).Out_Neighbours.Iterate loop
            declare
               Out_Node : constant Valid_Vertex_Id := Key (C);
            begin
               if not Will_Visit (Out_Node) then
                  Stack.Append (Out_Node);
                  Will_Visit (Out_Node) := True;
               end if;
            end;
         end loop;
      end loop;
   end DFS;

   ----------------------------------------------------------------------
   --  Graph-wide operations
   ----------------------------------------------------------------------

   function Invert (G : T'Class) return T
   is
      R : T;
   begin
      --  Start with an empty graph, with the same vertices.
      R := Create (G);

      --  Add reversed edges.
      for V_1 in Valid_Vertex_Id range 1 .. G.Vertices.Last_Index loop
         for C in G.Vertices (V_1).Out_Neighbours.Iterate loop
            declare
               V_2 : Valid_Vertex_Id renames Key (C);
               Atr : Edge_Attributes renames Element (C);
            begin
               R.Vertices (V_2).Out_Neighbours.Include (V_1, Atr);
               R.Vertices (V_1).In_Neighbours.Include (V_2);
            end;
         end loop;
      end loop;

      return R;
   end Invert;

   function Dominator_Tree_Internal (G : T'Class;
                                     R : Vertex_Id)
                                    return Vertex_To_Vertex_T
   is
      subtype V_To_V is Vertex_To_Vertex_T (0 .. G.Vertices.Last_Index);
      type V_To_VIL is array
        (Valid_Vertex_Id range 1 .. G.Vertices.Last_Index)
        of Vertex_Index_List;

      Parent, Ancestor, Child, Vertex : V_To_V;
      Label, Semi, Size               : V_To_V   := (others => 0);

      Bucket : V_To_VIL := (others => VIL.Empty_Vector);
      Dom    : V_To_V   := (others => 0);

      N : Vertex_Id := 0;

      procedure DT_DFS (V : Valid_Vertex_Id)
      is
      begin
         N         := N + 1;
         Label (V) := V;

         Semi (V)     := N;
         Vertex (N)   := Label (V);
         Child (V)    := 0;
         Ancestor (V) := 0;
         Size (V)     := 1;

         for C in G.Vertices (V).Out_Neighbours.Iterate loop
            declare
               W : Valid_Vertex_Id renames Key (C);
            begin
               if Semi (W) = 0 then
                  Parent (W) := V;
                  DT_DFS (W);
               end if;
               --  In_Neighbours is our version of Pred
            end;
         end loop;
      end DT_DFS;

      procedure Compress (V : Valid_Vertex_Id)
      is
      begin
         if Ancestor (Ancestor (V)) /= 0 then
            Compress (Ancestor (V));
            if Semi (Label (Ancestor (V))) < Semi (Label (V)) then
               Label (V) := Label (Ancestor (V));
            end if;
            Ancestor (V) := Ancestor (Ancestor (V));
         end if;
      end Compress;

      function Eval (V : Valid_Vertex_Id)
                    return Vertex_Id
      is
      begin
         if Ancestor (V) = 0 then
            return Label (V);
         else
            Compress (V);
            if Semi (Label (Ancestor (V))) >= Semi (Label (V)) then
               return Label (V);
            else
               return Label (Ancestor (V));
            end if;
         end if;
      end Eval;

      procedure Link (V, W : Valid_Vertex_Id)
      is
         S : Vertex_Id := W;

         procedure Swap (A, B : in out Vertex_Id)
         is
            Tmp : Vertex_Id := A;
         begin
            A := B;
            B := Tmp;
         end Swap;
      begin
         while Semi (Label (W)) < Semi (Label (Child (S))) loop
            if Size (S) + Size (Child (Child (S))) >= 2 * Size (Child (S)) then
               Ancestor (Child (S)) := S;
               Child (S)            := Child (Child (S));
            else
               Size (Child (S)) := Size (S);
               Ancestor (S)     := Child (S);
               S                := Child (S);
            end if;
         end loop;
         Label (S) := Label (W);
         Size (V)  := Size (V) + Size (W);
         if Size (V) < 2 * Size (W) then
            Swap (S, Child (V));
         end if;
         while S /= 0 loop
            Ancestor (S) := V;
            S            := Child (S);
         end loop;
      end Link;

   begin
      --  Step 1

      --  Pred is In_Neighbours and is already set.
      --  Bucket is initialised to be VIL.Empty_Vector, see above.
      --  Semi is already set to 0.

      DT_DFS (R);
      --  Size, Label and Semi are already set to 0, see above.

      for I in reverse Valid_Vertex_Id range 2 .. N loop
         declare
            W : constant Valid_Vertex_Id := Vertex (I);
         begin
            --  Step 2
            for V of G.Vertices (W).In_Neighbours loop
               declare
                  U : constant Vertex_Id := Eval (V);
               begin
                  if Semi (U) < Semi (W) then
                     Semi (W) := Semi (U);
                  end if;
               end;
            end loop;
            Bucket (Vertex (Semi (W))).Append (W);
            Link (Parent (W), W);

            --  Step 3
            while Bucket (Parent (W)).Length > 0 loop
               declare
                  V : constant Valid_Vertex_Id
                    := Bucket (Parent (W)).Last_Element;
                  U : constant Valid_Vertex_Id
                    := Eval (V);
               begin
                  Bucket (Parent (W)).Delete_Last;
                  if Semi (U) < Semi (V) then
                     Dom (V) := U;
                  else
                     Dom (V) := Parent (W);
                  end if;
               end;
            end loop;
         end;
      end loop;

      --  Step 4
      for I in Valid_Vertex_Id range 2 .. N loop
         declare
            W : constant Valid_Vertex_Id := Vertex (I);
         begin
            if Dom (W) /= Vertex (Semi (W)) then
               Dom (W) := Dom (Dom (W));
            end if;
         end;
      end loop;

      Dom (R) := 0;

      return Dom;
   end Dominator_Tree_Internal;

   function Dominator_Tree (G : T'Class;
                            R : Vertex_Id)
                           return T
   is
      Dom : Vertex_To_Vertex_T := Dominator_Tree_Internal (G, R);
      DT : T;
   begin
      DT := Create (G);
      for V in Valid_Vertex_Id range 1 .. Dom'Last loop
         if Dom (V) in Valid_Vertex_Id then
            DT.Add_Edge (Dom (V), V);
         end if;
      end loop;

      return DT;
   end Dominator_Tree;

   function Dominance_Frontier (G : T'Class;
                                R : Vertex_Id)
                               return T
   is
      Dom : Vertex_To_Vertex_T := Dominator_Tree_Internal (G, R);
      DF  : T                  := Create (G);
   begin
      for B in Valid_Vertex_Id range 1 .. G.Vertices.Last_Index loop
         if G.Vertices (B).In_Neighbours.Length >= 2 then
            for P of G.Vertices (B).In_Neighbours loop
               declare
                  Runner : Valid_Vertex_Id := P;
               begin
                  while Runner /= Dom (B) loop
                     Df.Add_Edge (B, Runner);
                     Runner := Dom (Runner);
                  end loop;
               end;
            end loop;
         end if;
      end loop;
      return DF;
   end Dominance_Frontier;

   procedure Close (G       : in out T'Class;
                    Visitor : access procedure (A, B : Vertex_Id))
   is
      type Component is new Natural;

      type Bit_Field is array
        (Valid_Vertex_Id range 1 .. G.Vertices.Last_Index) of Boolean;

      type V_To_V is array
        (Vertex_Id range 0 .. G.Vertices.Last_Index) of Vertex_Id;

      type V_To_VIS is array
        (Valid_Vertex_Id range 1 .. G.Vertices.Last_Index) of Vertex_Index_Set;

      type V_To_Comp is array
        (Valid_Vertex_Id range 1 .. G.Vertices.Last_Index) of Component;

      Visited   : Bit_Field         := Bit_Field'(others => False);
      Stack     : Vertex_Index_List := VIL.Empty_Vector;
      Root      : V_To_V            := V_To_V'(others => 0);
      Comp      : V_To_Comp         := V_To_Comp'(others => 0);
      Succ      : V_To_V            := V_To_V'(others => 0);
      Sets      : V_To_VIS          := V_To_VIS'(others => VIS.Empty_Set);

      Current_Component : Component := 0;

      procedure SIMPLE_TC (V : Valid_Vertex_Id)
      is
      begin
         Visited (V) := True;

         Root (V) := V;

         Stack.Append (V);

         Succ (V) := V;
         for C in G.Vertices (V).Out_Neighbours.Iterate loop
            declare
               W : Valid_Vertex_Id renames Key (C);
            begin
               Sets (Succ (V)).Include (W);
            end;
         end loop;

         for C in G.Vertices (V).Out_Neighbours.Iterate loop
            declare
               W : Valid_Vertex_Id renames Key (C);
            begin
               if not Visited (W) then
                  SIMPLE_TC (W);
               end if;
               if Comp (W) = 0 then
                  Root (V) := Vertex_Id'Min (Root (V), Root (W));
               end if;
               Sets (Succ (V)).Union (Sets (Succ (W)));
            end;
         end loop;

         if Root (V) = V then
            Current_Component := Current_Component + 1;
            loop
               declare
                  W : constant Valid_Vertex_Id := Stack.Last_Element;
               begin
                  Stack.Delete_Last;

                  Comp (W) := Current_Component;
                  Succ (W) := Succ (V); --  Pointer copy

                  exit when W = V;
               end;
            end loop;
         end if;
      end SIMPLE_TC;

   begin
      for V in Valid_Vertex_Id range 1 .. G.Vertices.Last_Index loop
         if not Visited (V) then
            SIMPLE_TC (V);
         end if;
      end loop;

      for V in Valid_Vertex_Id range 1 .. G.Vertices.Last_Index loop
         for W of Sets (Succ (V)) loop
            if not G.Edge_Exists (V, W) then
               Visitor (V, W);
               G.Add_Edge (V, W);
            end if;
         end loop;
      end loop;
   end Close;

   ----------------------------------------------------------------------
   --  IO
   ----------------------------------------------------------------------

   procedure Write_Dot_File (G        : T'Class;
                             Filename : String;
                             PP       : access function (V : Vertex_Key)
                                                        return String)
   is
   begin
      Put_Line ("digraph G {");
      Put_Line ("   graph [splines=True];");

      for I in Valid_Vertex_Id range 1 .. G.Vertices.Last_Index loop
         Put ("   ");
         Put (Valid_Vertex_Id'Image (I));
         Put (" [label=""");
         Put (PP (G.Vertices (I).Key));
         Put ("""];");
         New_Line;
      end loop;

      New_Line;

      for V_1 in Valid_Vertex_Id range 1 .. G.Vertices.Last_Index loop
         for C in G.Vertices (V_1).Out_Neighbours.Iterate loop
            declare
               V_2 : Valid_Vertex_Id renames Key (C);
               Atr : Edge_Attributes renames Element (C);
            begin
               Put ("   ");
               Put (Valid_Vertex_Id'Image (V_1));
               Put (" -> ");
               Put (Valid_Vertex_Id'Image (V_2));
               if Atr.Marked then
                  Put (" [color=blue]");
               end if;
               Put (";");
               New_Line;
            end;
         end loop;
      end loop;

      Put_Line ("}");
   end Write_Dot_File;

end Graph;
