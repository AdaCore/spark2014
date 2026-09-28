with SPARK.Containers.Functional.Infinite_Sequences;
with SPARK.Containers.Functional.Sets;
with SPARK.Pointers.Abstract_Reachability;
with SPARK.Pointers.Explicit_Reclamation.Global_Memory;
with SPARK.Pointers.Handles.Plain_Handles; use SPARK.Pointers.Handles;

--  Union-find (disjoint sets) over SPARK.Pointers.Explicit_Reclamation.
--  Global_Memory, with union by size.
--
--  The forest is held entirely in the modelled memory: a node is a cell whose
--  Parent handle is the null pointer exactly when the node is a root.
--
--  Termination of the parent chain comes from
--  SPARK.Pointers.Abstract_Reachability, instantiated on the Parent edge:
--  Is_Rooted is Is_Acyclic, and anything recursive over the chain decreases on
--  the size of the reachable set. Size is still stored in each cell, but only
--  because that is union by size and because Set_Size is a query a client
--  wants -- it is no longer load bearing for termination, and the invariant no
--  longer mentions it. An earlier version of this example did carry it for
--  that purpose, and paid for it with a third lemma; see Union below.

procedure Union_Find_Global with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type UF_Cell is record
      Parent : Plain_Handles.Handle;
      Size   : Positive;
   end record;

   function Is_Reclaimed (Unused : UF_Cell) return Boolean is (True)
   with Ghost => Static, Global => null;

   package UF is new
     SPARK.Pointers.Explicit_Reclamation.Global_Memory (UF_Cell, Is_Reclaimed);

   function Copy (C : UF_Cell) return UF_Cell is (C) with Global => null;
   package UF_Copy is new UF.Copy_Operations (Copy);

   use UF;
   use UF_Copy;
   use Handle_Operations;
   use Memory_Model;

   --  Reachability along the Parent edge. Cell_Parent is total, so the
   --  reachability theory never sees a handle.

   function Cell_Parent (C : UF_Cell) return Pointer
   is (if Valid_Handle (C.Parent) then Of_Handle (C.Parent) else Null_Pointer)
   with Ghost => Static, Global => null;

   --  The instances have to be ghost, and a ghost package is the only way to
   --  say so: an aspect on an instantiation is rejected.

   package Ghost_Containers with Ghost => Static is
      package Ptr_Sets is new SPARK.Containers.Functional.Sets (Pointer, "=");
      package Ptr_Seqs is new
        SPARK.Containers.Functional.Infinite_Sequences
          (Pointer, "=", Use_Logical_Equality => True);
   end Ghost_Containers;
   use Ghost_Containers;

   package Reach is new SPARK.Pointers.Abstract_Reachability
     (Memory_Maps   => Memory_Model.Pointer_To_Object_Maps,
      "="           => "=",
      Next          => Cell_Parent,
      Key_Sets      => Ptr_Sets,
      Key_Sequences => Ptr_Seqs);

   function Valid_Handles (M : Memory_Map) return Boolean
   is (for all A in M => Valid_Handle (Get (M, A).Parent))
   with Ghost => Static, Global => null;

   ----------------------------------------------------------------
   --  The model: a forest, expressed over the memory map alone.  --
   ----------------------------------------------------------------

   function Parent_Of (M : Memory_Map; P : Pointer) return Pointer is
     (Of_Handle (Get (M, P).Parent))
   with
     Ghost  => Static,
     Global => null,
     Pre    => In_Memory (M, P) and then Valid_Handle (Get (M, P).Parent);

   function Size_Of (M : Memory_Map; P : Pointer) return Positive is
     (Get (M, P).Size)
   with Ghost => Static, Global => null, Pre => In_Memory (M, P);

   --  P reaches a root by following parents: Is_Acyclic on the Parent edge.
   --  It stays a named wrapper rather than a direct call because the frame
   --  lemmas below attach to it with Automatic_Instantiation -- Valid_Forest
   --  quantifies over the whole memory, so there is no call site at which to
   --  invoke them by hand, and a client function is the only thing a lemma can
   --  be attached to.

   function Is_Rooted (M : Memory_Map; P : Pointer) return Boolean
   is (Reach.Is_Acyclic (P, M))
   with
     Ghost  => Static,
     Global => null,
     Pre    =>
       In_Memory (M, P)
       and then Reach.Valid_Memory (M)
       and then Valid_Handles (M);
   --  The two global conditions are a precondition rather than a conjunct: a
   --  frame lemma cannot re-establish them from Writes and Deallocates alone,
   --  so folding them in would make Is_Rooted (M2, P) unprovable.

   --  Lemma: being rooted survives any change that preserves every Parent --
   --  which is weaker than "writes to no cell", and is what lets it absorb the
   --  size-raising write of Union. With the size out of the invariant there is
   --  nothing else a write to a root could disturb. Attached to Is_Rooted with Automatic_Instantiation so it
   --  is available under the quantifier in Valid_Forest, where there is no
   --  call site at which to invoke it by hand.

   procedure Lemma_Rooted_Frame (M1, M2 : Memory_Map; P : Pointer)
   with
     Ghost              => Static,
     Global             => null,
     Annotate           => (GNATprove, Automatic_Instantiation),
     Pre                =>
       In_Memory (M1, P)
       and then Reach.Valid_Memory (M1)
       and then Valid_Handles (M1)
       and then Reach.Valid_Memory (M2)
       and then Valid_Handles (M2)
       and then Is_Rooted (M1, P)
       and then Deallocates (M1, M2, None)
       and then
         (for all A in M1 =>
            Cell_Parent (Get (M2, A).all) = Cell_Parent (Get (M1, A).all)),
     Post               =>
       Is_Rooted (M2, P) and then Root_Of (M2, P) = Root_Of (M1, P),
     Subprogram_Variant =>
       (Decreases => Ptr_Sets.Length (Reach.Reachable_Set (P, M1)));

   --  Lemma: linking root RP under root RQ, with Size RP < Size RQ, preserves
   --  rootedness everywhere and moves exactly the nodes whose root was RP.
   --  Also automatically instantiated: Union's postcondition quantifies over
   --  the whole memory, so again there is no call site.

   procedure Lemma_Link (M1, M2 : Memory_Map; RP, RQ, A : Pointer)
   with
     Ghost              => Static,
     Global             => null,
     Annotate           => (GNATprove, Automatic_Instantiation),
     Pre                =>
       In_Memory (M1, A)
       and then Reach.Valid_Memory (M1)
       and then Valid_Handles (M1)
       and then Reach.Valid_Memory (M2)
       and then Valid_Handles (M2)
       and then Is_Rooted (M1, A)
       and then In_Memory (M1, RP)
       and then In_Memory (M1, RQ)
       and then Valid_Handle (Get (M1, RP).Parent)
       and then Valid_Handle (Get (M1, RQ).Parent)
       and then Parent_Of (M1, RP) = Null_Pointer
       and then Parent_Of (M1, RQ) = Null_Pointer
       and then Size_Of (M1, RP) < Size_Of (M1, RQ)
       and then Allocates (M1, M2, None)
       and then Deallocates (M1, M2, None)
       and then Writes (M1, M2, Only (RP))
       and then In_Memory (M2, RP)
       and then Valid_Handle (Get (M2, RP).Parent)
       and then Parent_Of (M2, RP) = RQ
       and then Size_Of (M2, RP) = Size_Of (M1, RP),
     Post               =>
       Is_Rooted (M2, A)
       and then Root_Of (M2, A)
                = (if Root_Of (M1, A) = RP then RQ else Root_Of (M1, A)),
     Subprogram_Variant =>
       (Decreases => Ptr_Sets.Length (Reach.Reachable_Set (A, M1)));

   function Valid_Forest (M : Memory_Map) return Boolean is
     (Reach.Valid_Memory (M)
      and then Valid_Handles (M)
      and then (for all A in M => Is_Rooted (M, A)))
   with Ghost => Static, Global => null;

   function Root_Of (M : Memory_Map; P : Pointer) return Pointer is
     (if Parent_Of (M, P) = Null_Pointer
      then P
      else Root_Of (M, Parent_Of (M, P)))
   with
     Ghost              => Static,
     Global             => null,
     Pre                =>
       In_Memory (M, P)
       and then Reach.Valid_Memory (M)
       and then Valid_Handles (M)
       and then Is_Rooted (M, P),
     Post               =>
       In_Memory (M, Root_Of'Result)
       and then Valid_Handle (Get (M, Root_Of'Result).Parent)
       and then Parent_Of (M, Root_Of'Result) = Null_Pointer,
     Subprogram_Variant =>
       (Decreases => Ptr_Sets.Length (Reach.Reachable_Set (P, M)));

   --------------------
   --  Operations.   --
   --------------------

   procedure Make_Set (P : out Pointer)
   with
     Global => (In_Out => UF.Memory, Input => SPARK.Pointers.Memory_Addresses),
     Pre    => Valid_Forest (Model (Memory)),
     Post   =>
       Valid_Forest (Model (Memory))
       and then In_Memory (Model (Memory), P)
       and then Parent_Of (Model (Memory), P) = Null_Pointer
       and then Root_Of (Model (Memory), P) = P;

   function Find (P : Pointer) return Pointer
   with
     Global => UF.Memory,
     Pre    => Valid_Forest (Model (Memory)) and then In_Memory (Model (Memory), P),
     Post   => Find'Result = Root_Of (Model (Memory), P);

   function Set_Size (P : Pointer) return Positive
   with
     Global => UF.Memory,
     Pre    => Valid_Forest (Model (Memory)) and then In_Memory (Model (Memory), P),
     Post   =>
       Set_Size'Result = Size_Of (Model (Memory), Root_Of (Model (Memory), P));
   --  The size of P's set. Available because the size is stored on the side
   --  rather than being a property only of the model.

   procedure Union (P, Q : Pointer)
   with
     Global => (In_Out => UF.Memory),
     Pre    =>
       Valid_Forest (Model (Memory))
       and then In_Memory (Model (Memory), P)
       and then In_Memory (Model (Memory), Q)
       --  The two sets together must still be countable. Sizes are stored in
       --  the structure, so this is a statement about the data rather than
       --  about the memory model.
       and then (if Root_Of (Model (Memory), P) /= Root_Of (Model (Memory), Q)
                 then Size_Of (Model (Memory), Root_Of (Model (Memory), P))
                      <= Natural'Last
                         - Size_Of (Model (Memory), Root_Of (Model (Memory), Q))),
     Post   =>
       Valid_Forest (Model (Memory))
       and then Allocates (Model (Memory)'Old, Model (Memory), None)
       and then Deallocates (Model (Memory)'Old, Model (Memory), None)
       and then Root_Of (Model (Memory), P) = Root_Of (Model (Memory), Q)
       --  Every other node keeps its root, unless that root was the one that
       --  got linked. This is the frame property a client needs.
       and then (for all A in Model (Memory)'Old =>
                   Root_Of (Model (Memory), A)
                   = (if Root_Of (Model (Memory)'Old, A)
                         = Root_Of (Model (Memory)'Old, P)
                      then Root_Of (Model (Memory), P)
                      elsif Root_Of (Model (Memory)'Old, A)
                            = Root_Of (Model (Memory)'Old, Q)
                      then Root_Of (Model (Memory), Q)
                      else Root_Of (Model (Memory)'Old, A)));

   --------------
   --  Bodies  --
   --------------

   procedure Lemma_Rooted_Frame (M1, M2 : Memory_Map; P : Pointer) is
   begin
      if Parent_Of (M1, P) /= Null_Pointer then
         Lemma_Rooted_Frame (M1, M2, Parent_Of (M1, P));
      end if;
   end Lemma_Rooted_Frame;

   procedure Lemma_Link (M1, M2 : Memory_Map; RP, RQ, A : Pointer) is
   begin
      if A /= RP and then Parent_Of (M1, A) /= Null_Pointer then
         Lemma_Link (M1, M2, RP, RQ, Parent_Of (M1, A));
      end if;
   end Lemma_Link;

   procedure Make_Set (P : out Pointer) is
   begin
      Create_Copy ((Parent => Null_Handle, Size => 1), P);
   end Make_Set;

   function Find (P : Pointer) return Pointer is
      C : Pointer := P;
   begin
      while Of_Handle (Deref (C).Parent) /= Null_Pointer loop
         pragma Loop_Invariant (In_Memory (Model (Memory), C));
         pragma Loop_Invariant (Is_Rooted (Model (Memory), C));
         pragma Loop_Invariant
           (Root_Of (Model (Memory), C) = Root_Of (Model (Memory), P));
         pragma
           Loop_Variant
             (Decreases =>
                Ptr_Sets.Length (Reach.Reachable_Set (C, Model (Memory))));
         C := Of_Handle (Deref (C).Parent);
      end loop;
      return C;
   end Find;

   function Set_Size (P : Pointer) return Positive is (Deref (Find (P)).Size);

   procedure Union (P, Q : Pointer) is
      RP : constant Pointer := Find (P);
      RQ : constant Pointer := Find (Q);
   begin
      if RP = RQ then
         return;
      end if;

      declare
         Size_P : constant Positive := Deref (RP).Size;
         Size_Q : constant Positive := Deref (RQ).Size;
      begin
         --  The order of these two writes is free. An earlier version had to
         --  raise the new root's size *before* the link, because Is_Rooted
         --  carried the strict size increase and linking first broke it
         --  between two statements of one operation; that cost a third lemma,
         --  Lemma_Raise_Size. Is_Acyclic needs no such invariant, and the
         --  size-only write is absorbed by Lemma_Rooted_Frame above.
         if Size_P < Size_Q then
            Assign
              (RQ,
               (Parent => Null_Handle, Size => Size_P + Size_Q));
            Assign (RP, (Parent => To_Handle (RQ), Size => Size_P));
         else
            Assign
              (RP,
               (Parent => Null_Handle, Size => Size_P + Size_Q));
            Assign (RQ, (Parent => To_Handle (RP), Size => Size_Q));
         end if;
      end;
   end Union;

   ------------------------------------------------------------------
   --  The same framing question as Demo_Framing in the separate-   --
   --  memory version, but with both forests in the one memory.     --
   --  Compare the preconditions: here the client must *state and   --
   --  carry* that R lies in a different tree, because nothing else --
   --  distinguishes the two forests. With separate memories that   --
   --  hypothesis is not needed at all -- a different memory is a   --
   --  different parameter.                                        --
   ------------------------------------------------------------------

   procedure Demo_Framing (P, Q, R : Pointer)
   with
     Global => (In_Out => UF.Memory),
     Pre    =>
       Valid_Forest (Model (Memory))
       and then In_Memory (Model (Memory), P)
       and then In_Memory (Model (Memory), Q)
       and then In_Memory (Model (Memory), R)
       and then (if Root_Of (Model (Memory), P) /= Root_Of (Model (Memory), Q)
                 then Size_Of (Model (Memory), Root_Of (Model (Memory), P))
                      <= Natural'Last
                         - Size_Of (Model (Memory), Root_Of (Model (Memory), Q)))
       --  Needed here, and only here: R must be known not to share a tree
       --  with P or Q.
       and then Root_Of (Model (Memory), R) /= Root_Of (Model (Memory), P)
       and then Root_Of (Model (Memory), R) /= Root_Of (Model (Memory), Q),
     Post   =>
       Valid_Forest (Model (Memory))
       and then In_Memory (Model (Memory), R)
       and then Root_Of (Model (Memory), R)
                = Root_Of (Model (Memory)'Old, R)
       and then Root_Of (Model (Memory), P) = Root_Of (Model (Memory), Q)
   is
   begin
      Union (P, Q);
   end Demo_Framing;

begin
   null;
end Union_Find_Global;
