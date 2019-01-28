pragma Ada_2012;
with Ada.Unchecked_Conversion;
with Ada.Unchecked_Deallocation;
with System.Memory;                 use System, System.Memory;
with System.Unsigned_Types;         use System.Unsigned_Types;

package body Conts.Lists is

   -------------------------------
   -- Bounded_List_Nodes_Traits --
   -------------------------------

   package body Bounded_List_Nodes_Traits is

      --------------
      -- Allocate --
      --------------

      procedure Allocate
         (Self    : in out Nodes_List'Class;
          Element : Stored_Element_Type;
          N       : out Node_Access)
      is
      begin
         if Self.Free > 0 then
            N := Node_Access (Self.Free);
            Self.Free := Integer (Self.Nodes (Count_Type (N)).Next);
         else
            N := Node_Access (abs Self.Free + 1);
            Self.Free := Self.Free - 1;
         end if;

         if Count_Type (N) <= Self.Nodes'Last then
            Self.Nodes (Count_Type (N)) :=
               (Element  => Element,
                Previous => Null_Node_Access,
                Next     => Null_Node_Access);
         else
            N := Null_Node_Access;
         end if;
      end Allocate;

      --------------
      -- Set_Next --
      --------------

      procedure Set_Next
         (Self : in out Nodes_List'Class; N, Next : Node_Access) is
      begin
         Self.Nodes (Count_Type (N)).Next := Next;
      end Set_Next;

      ------------------
      -- Set_Previous --
      ------------------

      procedure Set_Previous
         (Self : in out Nodes_List'Class; N, Previous : Node_Access) is
      begin
         Self.Nodes (Count_Type (N)).Previous := Previous;
      end Set_Previous;

      ------------
      -- Assign --
      ------------

      procedure Assign
         (Nodes    : in out Nodes_List'Class;
          Source   : Nodes_List'Class;
          New_Head : out Node_Access;
          Old_Head : Node_Access;
          New_Tail : out Node_Access;
          Old_Tail : Node_Access)
      is
         N : Node_Access;
      begin
         --  Indices will remain the same
         New_Head := Old_Head;
         New_Tail := Old_Tail;

         Nodes.Free  := Source.Free;

         --  We need to copy each of the elements.

         if not Elements.Use_Implicit_Copy then
            N := Old_Head;
            while N /= Null_Node_Access loop
               declare
                  Value : Node renames Source.Nodes (Count_Type (N));
               begin
                  Nodes.Nodes (Count_Type (N)) :=
                     (Element  => Elements.Convert_From
                        (Elements.Convert_To (Value.Element)),
                      Next     => Value.Next,
                      Previous => Value.Previous);
                  N := Value.Next;
               end;
            end loop;
         end if;
      end Assign;

   end Bounded_List_Nodes_Traits;

   ---------------------------------
   -- Unbounded_List_Nodes_Traits --
   ---------------------------------

   package body Unbounded_List_Nodes_Traits is

      procedure Unchecked_Free is new Ada.Unchecked_Deallocation
         (Node, Node_Access);

      --------------
      -- Allocate --
      --------------

      procedure Allocate
         (Self    : in out Nodes_Container'Class;
          Element : Elements.Stored_Element_Type;
          N       : out Node_Access)
      is
         pragma Unreferenced (Self);
      begin
         N := new Node;
         if N /= null then
            N.Element := Element;
         end if;
      end Allocate;

      ------------------
      -- Release_Node --
      ------------------

      procedure Release_Node
         (Self : in out Nodes_Container'Class; N : in out Node_Access)
      is
         pragma Unreferenced (Self);
      begin
         Unchecked_Free (N);
      end Release_Node;

      --------------
      -- Set_Next --
      --------------

      procedure Set_Next
         (Self : in out Nodes_Container'Class; N, Next : Node_Access)
      is
         pragma Unreferenced (Self);
      begin
         N.Next := Next;
      end Set_Next;

      ------------------
      -- Set_Previous --
      ------------------

      procedure Set_Previous
         (Self : in out Nodes_Container'Class; N, Previous : Node_Access)
      is
         pragma Unreferenced (Self);
      begin
         N.Previous := Previous;
      end Set_Previous;

      ------------
      -- Assign --
      ------------

      procedure Assign
         (Nodes    : in out Nodes_Container'Class;
          Source   : Nodes_Container'Class;
          New_Head : out Node_Access;
          Old_Head : Node_Access;
          New_Tail : out Node_Access;
          Old_Tail : Node_Access)
      is
         pragma Unreferenced (Source, Old_Tail);
         N, Tmp, Tmp2 : Node_Access;
      begin
         if Old_Head = null then
            New_Head := null;
            New_Tail := null;
            return;
         end if;

         Tmp2 := Old_Head;
         Allocate
            (Nodes,
            Elements.Convert_From (Elements.Convert_To (Tmp2.Element)),
            Tmp);
         New_Head := Tmp;

         loop
            Tmp2 := Tmp2.Next;
            exit when Tmp2 = null;

            Allocate (Nodes, Elements.Convert_From
               (Elements.Convert_To (Tmp2.Element)), N);
            Set_Next (Nodes, Tmp, N);
            Set_Previous (Nodes, N, Tmp);
            Tmp := N;
         end loop;

         New_Tail := N;
      end Assign;

   end Unbounded_List_Nodes_Traits;

   ---------------------------------------
   -- SPARK_Unbounded_List_Nodes_Traits --
   ---------------------------------------

   package body SPARK_Unbounded_List_Nodes_Traits with SPARK_Mode => Off is

      package body Private_Nodes_List with SPARK_Mode => Off is

         pragma Warnings (Off);  --  no aliasing issue
         function Convert is new Ada.Unchecked_Conversion
           (Nodes_Array_Access, System.Address);
         function Convert is new Ada.Unchecked_Conversion
           (System.Address, Nodes_Array_Access);
         pragma Warnings (On);

         --------------
         -- Allocate --
         --------------

         procedure Allocate
           (Self    : in out Nodes_List'Class;
            Element : Elements.Stored_Element_Type;
            N       : out Node_Access)
         is
            New_Size : System.Unsigned_Types.Unsigned := 4;
            S : size_t;
         begin
            --  Reuse empty slots if possible
            if Self.Free > 0 then
               N := Node_Access (Self.Free);
               Self.Free := Integer (Self.Nodes (Count_Type (N)).Next);
            else
               N := Node_Access (abs Self.Free + 1);
               Self.Free := Self.Free - 1;
            end if;

            --  Grow the table of nodes if needed

            if Count_Type (N) > Self.Last then
               --  Use the same allocation scheme as in python, in an effort to
               --  find a good tradeoff to allocate a lot of memory and be
               --  efficient. Growth pattern is 0, 4, 8, 16, 25, 35, 46, 58,
               --  72, 88, 106, 126, 148, 173, 201, 233, 269, 309, 354, 405,...
               --  The over-allocation is mild, but is enough to give
               --  linear-time amortized behavior of a long sequence of
               --  appends.
               --
               --  Performance: adding 300_000 items with this scheme:
               --       265% of the time needed for C++ STL
               --  With the scheme were the size is multiplied by 1.5:
               --       137% of the time needed for C++ STL
               --  When multiplying by 2: similar to multiplying by 1.5

               --  New_Size := Unsigned (N);   --  minimal needed size
               --  New_Size := New_Size + Shift_Right (New_Size, 3) +
               --     (if New_Size < 9 then 3 else 6);

               New_Size := Unsigned'Max
                 (Unsigned (Count_Type'Max (Self.Last, 1) * 3 / 2),
                  Unsigned (N));
               Self.Last := Count_Type (New_Size);

               S := size_t (Self.Last * Node'Size / System.Storage_Unit);

               if Self.Nodes = null then
                  Self.Nodes := Convert (Alloc (S));
               else
                  Self.Nodes := Convert (Realloc (Convert (Self.Nodes), S));
               end if;
            end if;

            Self.Nodes (Count_Type (N)) :=
              (Element  => Element,
               Previous => Null_Node_Access,
               Next     => Null_Node_Access);
         end Allocate;

         ------------
         -- Assign --
         ------------

         procedure Assign
           (Nodes    : in out Nodes_List'Class;
            Source   : Nodes_List'Class;
            New_Head : out Node_Access;
            Old_Head : Node_Access;
            New_Tail : out Node_Access;
            Old_Tail : Node_Access)
         is
            S : size_t;
            N : Node_Access;
         begin
            --  We *must* preserve the indices
            New_Head := Old_Head;
            New_Tail := Old_Tail;

            S := size_t
              (Source.Last * Source.Nodes'Component_Size
               / System.Storage_Unit);
            Nodes.Nodes := Convert (Alloc (S));

            Nodes.Last := Source.Last;
            Nodes.Free := Source.Free;

            if Elements.Use_Implicit_Copy then
               Nodes.Nodes (1 .. Nodes.Last) :=
                 Source.Nodes (1 .. Source.Last);
            else
               N := Old_Head;
               while N /= Null_Node_Access loop
                  declare
                     Value : Node renames Source.Nodes (Count_Type (N));
                  begin
                     Nodes.Nodes (Count_Type (N)) :=
                       (Element  => Elements.Convert_From
                          (Elements.Convert_To (Value.Element)),
                        Next     => Value.Next,
                        Previous => Value.Previous);
                     N := Value.Next;
                  end;
               end loop;
            end if;
         end Assign;

         -------------
         -- Release --
         -------------

         procedure Release (Self : in out Nodes_List'Class) is
         begin
            System.Memory.Free (Convert (Self.Nodes));
            Self.Nodes := null;
            Self.Last := 0;
            Self.Free := 0;
         end Release;

         --------------
         -- Set_Next --
         --------------

         procedure Set_Next
           (Self : in out Nodes_List'Class; N, Next : Node_Access) is
         begin
            Self.Nodes (Count_Type (N)).Next := Next;
         end Set_Next;

         ------------------
         -- Set_Previous --
         ------------------

         procedure Set_Previous
           (Self : in out Nodes_List'Class; N, Previous : Node_Access) is
         begin
            Self.Nodes (Count_Type (N)).Previous := Previous;
         end Set_Previous;
      end Private_Nodes_List;

   end SPARK_Unbounded_List_Nodes_Traits;

   -------------------
   -- Generic_Lists --
   -------------------

   package body Generic_Lists with SPARK_Mode => Off is
      use Nodes;

      ------------
      -- Append --
      ------------

      procedure Append
         (Self    : in out List'Class;
          Element : Element_Type)
      is
         N : Node_Access;
      begin
         Allocate
            (Self,
             Nodes.Elements.Convert_From (Element),
             New_Node => N);

         if Enable_Asserts and then N = Null_Access then
            raise Storage_Error with "Allocating node failed";
         end if;

         if Self.Tail = Null_Access then
            Self.Tail := N;
            Self.Head := Self.Tail;
         else
            Set_Next (Self, Self.Tail, Next => N);
            Set_Previous (Self, N, Previous => Self.Tail);
            Self.Tail := N;
         end if;

         Self.Size := Self.Size + 1;
      end Append;

      -----------
      -- Clear --
      -----------

      procedure Clear (Self : in out List'Class) is
         C : Cursor := Self.First;
         N : Cursor;
         E : Stored_Element_Type;
      begin
         while Self.Has_Element (C) loop
            N := Self.Next (C);
            E := Self.Stored_Element (C);
            Elements.Release (E);
            Nodes.Release_Node (Self, C.Current);
            C := N;
         end loop;
         Nodes.Release (Self);

         Self.Head := Nodes.Null_Access;
         Self.Tail := Nodes.Null_Access;
         Self.Size := 0;
      end Clear;

      ------------
      -- Length --
      ------------

      function Length (Self : List'Class) return Count_Type is
      begin
         return Self.Size;
      end Length;

      -----------
      -- First --
      -----------

      function First (Self : List'Class) return Cursor is
      begin
         return (Current => Self.Head);
      end First;

      -------------
      -- Element --
      -------------

      function Element
         (Self : List'Class; Position : Cursor) return Element_Type is
      begin
         if Enable_Asserts and then Position.Current = Null_Access then
            raise Program_Error with "Invalid position in list";
         end if;

         return Nodes.Elements.Convert_To
            (Get_Element (Self, Position.Current));
      end Element;

      --------------------
      -- Stored_Element --
      --------------------

      function Stored_Element
         (Self : List'Class; Position : Cursor) return Stored_Element_Type is
      begin
         if Enable_Asserts and then Position.Current = Null_Access then
            raise Program_Error with "Invalid position in list";
         end if;

         return Get_Element (Self, Position.Current);
      end Stored_Element;

      -----------------
      -- Has_Element --
      -----------------

      function Has_Element
         (Self : List'Class; Position : Cursor) return Boolean
      is
         pragma Unreferenced (Self);
      begin
         return Position.Current /= Null_Access;
      end Has_Element;

      ----------
      -- Next --
      ----------

      function Next
         (Self : List'Class; Position : Cursor) return Cursor is
      begin
         if Position.Current = Null_Access then
            return Position;
         else
            return (Current => Get_Next (Self, Position.Current));
         end if;
      end Next;

      --------------
      -- Previous --
      --------------

      function Previous
         (Self : List'Class; Position : Cursor) return Cursor is
      begin
         if Position.Current = Null_Access then
            return Position;
         else
            return (Current => Get_Previous (Self, Position.Current));
         end if;
      end Previous;

      ----------
      -- Next --
      ----------

      procedure Next (Self : List'Class; Position : in out Cursor) is
      begin
         Position := Next (Self, Position);
      end Next;

      --------------
      -- Finalize --
      --------------

      procedure Finalize (Self : in out List) is
      begin
         Clear (Self);
      end Finalize;

      ------------
      -- Adjust --
      ------------

      procedure Adjust (Self : in out List) is
      begin
         Nodes.Assign (Self, Self,
                       Self.Head, Self.Head,
                       Self.Tail, Self.Tail);
      end Adjust;

      ------------
      -- Assign --
      ------------

      procedure Assign (Self : in out List'Class; Source : List'Class) is
      begin
         if Self'Address = Source'Address then
            --  Tagged types are always passed by reference, so we know they
            --  are the same, and do nothing.
            return;
         end if;

         Nodes.Assign (Self, Source,
                       Self.Head, Source.Head,
                       Self.Tail, Source.Tail);
      end Assign;

   end Generic_Lists;

end Conts.Lists;
