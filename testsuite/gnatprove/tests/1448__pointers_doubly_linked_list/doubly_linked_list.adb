pragma Extensions_Allowed (On);

with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Functional.Infinite_Sequences;
with SPARK.Containers.Functional.Sets;
with SPARK.Pointers.Abstract_Reachability;
with SPARK.Pointers.Auto_Reclaimed.Global_Memory;
with SPARK.Pointers.Handles.Auto_Reclaimed_Handles;

--  A doubly linked list over SPARK.Pointers.Auto_Reclaimed.Global_Memory.
--
--  This is the structure the unit's header names as the reason weak handles
--  exist. Every cell is reachable from its predecessor and from its
--  successor, so if both edges were strong each cell would hold its
--  neighbour's count above zero and no cell would ever be reclaimed
--  silently, because reclamation is invisible in the model and the leaking
--  program still proves.
--
--  So the forward edge is a strong handle and the backward edge a weak one.
--  The list is held by a pointer to its first cell, each cell keeps its
--  successor alive, and nothing keeps a predecessor alive. Dropping the head
--  reclaims the whole chain.
--
--  The list invariant, the traversals and Witness are all written over
--  SPARK.Pointers.Abstract_Reachability, instantiated on the Next edge.

procedure Doubly_Linked_List with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   package Cell_Handles is new
     SPARK.Pointers.Handles.Auto_Reclaimed_Handles.With_Weak_Handles;
   use Cell_Handles;

   type D_Cell is record
      Value : Integer;
      Next  : Strong_Handle;
      Prev  : Weak_Handle;
   end record;

   package Cells is new SPARK.Pointers.Auto_Reclaimed.Global_Memory (D_Cell);
   use Cells;
   use Cells.Memory_Model;

   type List is record
      First : Pointer;
      Last  : Weak_Handle;
   end record;

   package Ops is new Cells.Handle_Operations (Cell_Handles);
   use Ops;

   function Copy_Cell (C : D_Cell) return D_Cell
   is (C);
   package Cell_Ops is new Cells.Copy_Operations (Copy_Cell);
   use Cell_Ops;

   --  Reachability along the Next edge.
   --
   --  Cell_Next is total: it maps a cell whose handle is not valid to
   --  Null_Pointer rather than carrying a precondition.

   function Cell_Next (C : D_Cell) return Pointer
   is (if Valid_Handle (C.Next) then Of_Strong_Handle (C.Next) else Null_Pointer)
   with Ghost => Static, Global => null;

   package Ghost_Containers
     with Ghost => Static
   is
      package Ptr_Sets is new SPARK.Containers.Functional.Sets (Pointer, "=");
      package Ptr_Seqs is new
        SPARK.Containers.Functional.Infinite_Sequences
          (Pointer,
           "=",
           Use_Logical_Equality => True);
   end Ghost_Containers;
   use Ghost_Containers;

   package Reach is new
     SPARK.Pointers.Abstract_Reachability
       (Memory_Maps   => Cells.Memory_Model.Pointer_To_Object_Maps,
        "="           => "=",
        Next          => Cell_Next,
        Key_Sets      => Ptr_Sets,
        Key_Sequences => Ptr_Seqs);

   ------------------------
   --  The list invariant --
   ------------------------

   procedure Lemma_Length_Included (A, B : Ptr_Sets.Set)
   with
     Ghost  => Static,
     Global => null,
     Pre    => Ptr_Sets."<=" (A, B),
     Post   => Ptr_Sets.Length (A) <= Ptr_Sets.Length (B);
   --  Inclusion orders lengths

   procedure Lemma_Length_Included (A, B : Ptr_Sets.Set) is
   begin
      pragma
        Assert (Static => Ptr_Sets.Num_Overlaps (A, B) = Ptr_Sets.Length (A));
   end Lemma_Length_Included;

   function Valid_Sublist
     (F : Pointer; L : Pointer; M : Memory_Map) return Boolean
   is ((F = Null_Pointer and L = Null_Pointer)
       or else
         (In_Memory (M, F)
          and then Valid_Handle (Get (M, F).Next)
          and then
            (if Of_Strong_Handle (Get (M, F).Next) = Null_Pointer
             then F = L
             else
               (In_Memory (M, Of_Strong_Handle (Get (M, F).Next))
                and then
                  Valid_Handle (Get (M, Of_Strong_Handle (Get (M, F).Next)).Prev)
                and then
                  Peek (Get (M, Of_Strong_Handle (Get (M, F).Next)).Prev) = F
                and then
                  Valid_Sublist (Of_Strong_Handle (Get (M, F).Next), L, M)))))
   with
     Ghost              => Static,
     Global             => null,
     Pre                =>
       (F = Null_Pointer
        or else (In_Memory (M, F) and then Valid_Handle (Get (M, F).Prev)))
       and then Reach.Valid_Memory (M)
       and then Reach.Is_Acyclic (F, M),
     Post               =>
       (if Valid_Sublist'Result
        then
          (if F = Null_Pointer
           then L = Null_Pointer
           else
             (In_Memory (M, L)
              and Reach.Reachable (F, M, L)
              and Of_Strong_Handle (Get (M, L).Next) = Null_Pointer))
          and
            (for all A of Reach.Reachable_Set (F, M) =>
               Valid_Handle (Get (M, A).Next) and Valid_Handle (Get (M, A).Prev))),
     Subprogram_Variant =>
       (Decreases => Ptr_Sets.Length (Reach.Reachable_Set (F, M)));
   --  Each successor points back weakly at its predecessor

   procedure Lemma_Valid_Sublist_Preserved
     (F : Pointer; L : Pointer; M1, M2 : Memory_Map)
   with
     Ghost              => Static,
     Global             => null,
     Pre                =>
       (F = Null_Pointer or else (In_Memory (M1, F) and In_Memory (M2, F)))
       and then Reach.Valid_Memory (M1)
       and then Reach.Valid_Memory (M2)
       and then Reach.Is_Acyclic (F, M1)
       and then
         (F = Null_Pointer
          or else
            (Valid_Handle (Get (M1, F).Prev) and then Valid_Handle (Get (M2, F).Prev)))
       and then Valid_Sublist (F, L, M1)
       and then
         (for all A of Reach.Reachable_Set (F, M1) =>
            In_Memory (M2, A)
            and then Valid_Handle (Get (M2, A).Next)
            and then Cell_Next (Get (M2, A).all) = Cell_Next (Get (M1, A).all)
            and then
              (if A /= F
               then
                 Valid_Handle (Get (M2, A).Prev)
                 and then Get (M2, A).Prev = Get (M1, A).Prev)),
     Post               =>
       Reach.Is_Acyclic (F, M2) and then Valid_Sublist (F, L, M2),
     Subprogram_Variant =>
       (Decreases => Ptr_Sets.Length (Reach.Reachable_Set (F, M1)));
   --  A chain survives a write to a cell that is not on it

   procedure Lemma_Valid_Sublist_Preserved
     (F : Pointer; L : Pointer; M1, M2 : Memory_Map) is
   begin
      Reach.Lemma_Is_Acyclic_Preserved (F, M1, M2);
      if F /= Null_Pointer and then Cell_Next (Get (M1, F).all) /= Null_Pointer
      then
         Reach.Lemma_Reachable_Is_Acyclic (F, Cell_Next (Get (M1, F).all), M1);
         Lemma_Valid_Sublist_Preserved
           (Cell_Next (Get (M1, F).all), L, M1, M2);
      end if;
   end Lemma_Valid_Sublist_Preserved;

   function Valid_List (L : List; M : Memory_Map) return Boolean
   is ((L.First = Null_Pointer or else In_Memory (M, L.First))
       and then Reach.Valid_Memory (M)
       and then Reach.Is_Acyclic (L.First, M)
       and then
         (L.First = Null_Pointer
          or else
            (Valid_Handle (Get (M, L.First).Prev)
             and then Peek (Get (M, L.First).Prev) = Null_Pointer))
       and then Valid_Handle (L.Last)
       and then Valid_Sublist (L.First, Peek (L.Last), M))
   with Ghost => Static, Global => null;

   --  Walking backwards is the asymmetric half. Prev makes no claim on the
   --  cell it designates, so converting it back is only meaningful while that
   --  cell is still alive. Of_Weak_Handle would hand back a null pointer when
   --  it is not, which is no use in a proof, so the deterministic conversion
   --  is the one to use here.
   --
   --  What supports a backward step is that the target is reachable from the
   --  head: the head is held by a Pointer, a counted strong reference, and
   --  every cell reached from it is held by the chain of strong handles, so a
   --  Prev into that chain cannot dangle. In_List says exactly that, and
   --  Witness makes it operational by walking forward from the head.

   function In_List (P : Pointer; L : List) return Boolean
   is (Valid_List (L, Model)
       and then In_Memory (Model, P)
       and then Reach.Reachable (L.First, Model, P))
   with Ghost => Static, Global => Cells.Memory;

   function Witness (H : Weak_Handle; L : List) return Pointer
   with
     Global => Cells.Memory,
     Pre    => (Static => Valid_Handle (H) and then In_List (Peek (H), L)),
     Post   => (Static => Peek (H) = Witness'Result);

   function Next (L : List; P : Pointer) return Pointer
   with
     Global => Cells.Memory,
     Pre    => (Static => In_List (P, L)),
     Post   =>
       (Static =>
          Next'Result = Of_Strong_Handle (Get (Model, P).Next)
          and then (if P /= Peek (L.Last) then Next'Result /= Null_Pointer)
          and then
            (Next'Result = Null_Pointer or else In_List (Next'Result, L))
          and then
            Ptr_Sets.Length (Reach.Reachable_Set (Next'Result, Model))
            < Ptr_Sets.Length (Reach.Reachable_Set (P, Model)));
   --  One forward step, from a cell already known to be in the list

   function Previous (L : List; P : Pointer) return Pointer
   with
     Global => Cells.Memory,
     Pre    => In_List (P, L),
     Post   =>
       (Static =>
          Previous'Result = Peek (Get (Model, P).all.Prev)
          and then (if P /= L.First then Previous'Result /= Null_Pointer)
          and then
            (Previous'Result = Null_Pointer
             or else
               (In_List (Previous'Result, L)
                and then
                  Ptr_Sets.Length
                    (Reach.Reachable_Set (Previous'Result, Model))
                  > Ptr_Sets.Length (Reach.Reachable_Set (P, Model)))));

   function Witness (H : Weak_Handle; L : List) return Pointer is
      C : Pointer := L.First;
   begin
      loop
         pragma Loop_Invariant (Static => In_List (C, L));
         pragma
           Loop_Invariant (Static => Reach.Reachable (C, Model, Peek (H)));
         pragma
           Loop_Variant
             (Static =>
                (Decreases =>
                   Ptr_Sets.Length (Reach.Reachable_Set (C, Model))));

         declare
            W : constant Weak_Handle := To_Weak_Handle (C);
         begin
            if W = H then
               return C;
            end if;
            pragma Assert (Static => Peek (W) = C);
            pragma Assert (Static => C /= Peek (H));
         end;

         declare
            S : constant Pointer := Next (L, C);
         begin
            Reach.Lemma_Reachable_Is_Acyclic (L.First, C, Model);
            pragma Assert (Static => S /= Null_Pointer);
            pragma Assert (Static => Reach.Reachable (S, Model, Peek (H)));
            C := S;
         end;
      end loop;
   end Witness;

   package Back is new Ops.Witnessed_Conversions (List, In_List, Witness);

   function Next (L : List; P : Pointer) return Pointer is
      R : constant Pointer := Of_Strong_Handle (Deref (P).Next);
   begin
      Reach.Lemma_Reachable_Ordered (L.First, P, Peek (L.Last), Model);
      Reach.Lemma_Reachable_Is_Acyclic (L.First, P, Model);
      if R /= Null_Pointer then
         Reach.Lemma_Reachable_Transitive (L.First, P, R, Model);
      end if;
      return R;
   end Next;

   procedure Lemma_Prev_Of_Valid (F, L, P : Pointer; M : Memory_Map)
   with
     Ghost              => Static,
     Global             => null,
     Pre                =>
       In_Memory (M, F)
       and then Valid_Handle (Get (M, F).Prev)
       and then Reach.Valid_Memory (M)
       and then Reach.Is_Acyclic (F, M)
       and then Valid_Sublist (F, L, M)
       and then In_Memory (M, P)
       and then Reach.Reachable (F, M, P)
       and then F /= P,
     Post               =>
       Valid_Handle (Get (M, P).Prev)
       and then In_Memory (M, Peek (Get (M, P).Prev))
       and then Reach.Reachable (F, M, Peek (Get (M, P).Prev))
       and then Cell_Next (Get (M, Peek (Get (M, P).Prev)).all) = P,
     Subprogram_Variant =>
       (Decreases => Ptr_Sets.Length (Reach.Reachable_Set (F, M)));

   procedure Lemma_Prev_Of_Valid (F, L, P : Pointer; M : Memory_Map) is
   begin
      if P /= Cell_Next (Get (M, F).all) then
         Lemma_Prev_Of_Valid (Cell_Next (Get (M, F).all), L, P, M);
      end if;
   end Lemma_Prev_Of_Valid;

   function Previous (L : List; P : Pointer) return Pointer is
   begin
      if P /= L.First then
         Lemma_Prev_Of_Valid (L.First, Peek (L.Last), P, Model);
      end if;
      declare
         R : constant Pointer := Back.Of_Weak_Handle (Deref (P).Prev, L);
      begin
         if R /= Null_Pointer then
            Reach.Lemma_Reachable_Is_Acyclic (L.First, R, Model);
            Reach.Lemma_Reachable_Transitive (L.First, R, P, Model);
         end if;
         return R;
      end;
   end Previous;

   ----------------
   --  Push_Front --
   ----------------

   procedure Push_Front (L : in out List; V : Integer)
   with
     Global =>
       (In_Out => Cells.Memory, Input => SPARK.Pointers.Memory_Addresses),
     Pre    => (Static => Valid_List (L, Model)),
     Post   =>
       (Static =>
          Valid_List (L, Model)
          and then L.First /= Null_Pointer
          and then Monotonous_Memory (Model'Old, Model));

   procedure Push_Front (L : in out List; V : Integer) is
      Old_Head : constant Pointer := L.First;
      Old_M    : constant Memory_Map := Model
      with Ghost => Static;
      New_Head : Pointer;
   begin
      Create_Copy
        ((Value => V,
          Next  => To_Strong_Handle (Old_Head),
          Prev  => Null_Weak_Handle),
         New_Head);

      if Old_Head = Null_Pointer then
         L.Last := To_Weak_Handle (New_Head);
      else
         declare
            C : constant D_Cell := Deref (Old_Head);
         begin
            Assign
              (Old_Head,
               (Value => C.Value,
                Next  => C.Next,
                Prev  => To_Weak_Handle (New_Head)));
         end;

         --  Only Old_Head was written and only its Prev changed, so no Next
         --  on the old chain moved and the old model is intact.
         Reach.Lemma_Is_Acyclic_Preserved (Old_Head, Old_M, Model);
         Reach.Lemma_Is_Acyclic_Preserved (Old_Head, Old_M, Model);
         Reach.Lemma_Reachable_Preserved (Old_Head, Old_M, Model);
         Lemma_Valid_Sublist_Preserved (Old_Head, Peek (L.Last), Old_M, Model);
      end if;

      L.First := New_Head;
   end Push_Front;

   -------------------------
   --  The two traversals --
   -------------------------

   function Sum_Forward (L : List) return Big_Integer
   with Global => Cells.Memory, Pre => (Static => Valid_List (L, Model));

   function Sum_Forward (L : List) return Big_Integer is
      C : Pointer := L.First;
      S : Big_Integer := 0;
   begin
      while C /= Null_Pointer loop
         pragma Loop_Invariant (Static => In_List (C, L));
         pragma
           Loop_Variant
             (Static =>
                (Decreases =>
                   Ptr_Sets.Length (Reach.Reachable_Set (C, Model))));
         S := S + To_Big_Integer (Deref (C).Value);
         C := Next (L, C);
      end loop;
      return S;
   end Sum_Forward;

   function Sum_Backward (L : List) return Big_Integer
   with Global => Cells.Memory, Pre => (Static => Valid_List (L, Model));

   function Sum_Backward (L : List) return Big_Integer is
      S : Big_Integer := 0;
      C : Pointer := Back.Of_Weak_Handle (L.Last, L);
   begin
      while C /= Null_Pointer loop
         Reach.Lemma_Reachable_Included (L.First, C, Model);
         Lemma_Length_Included
           (Reach.Reachable_Set (C, Model),
            Reach.Reachable_Set (L.First, Model));
         pragma Loop_Invariant (Static => In_List (C, L));
         pragma
           Loop_Variant
             (Static =>
                (Decreases =>
                   Ptr_Sets.Length (Reach.Reachable_Set (L.First, Model))
                   - Ptr_Sets.Length (Reach.Reachable_Set (C, Model))));
         S := S + To_Big_Integer (Deref (C).Value);
         C := Previous (L, C);
      end loop;

      return S;
   end Sum_Backward;

begin
   null;
end Doubly_Linked_List;
