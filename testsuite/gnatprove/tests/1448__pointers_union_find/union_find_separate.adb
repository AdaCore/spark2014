with SPARK.Containers.Functional.Infinite_Sequences;
with SPARK.Containers.Functional.Sets;
with SPARK.Pointers.Abstract_Reachability;
with SPARK.Pointers.Explicit_Reclamation.Separate_Memory;
with SPARK.Pointers.Handles.Plain_Handles; use SPARK.Pointers.Handles;

--  The same union-find as union_find_global.adb, over
--  SPARK.Pointers.Explicit_Reclamation.Separate_Memory.
--
--  The model, the two lemmas and the algorithm are identical; only the
--  memory is now an object passed as a parameter. As in the global version,
--  rootedness is Is_Acyclic from SPARK.Pointers.Abstract_Reachability on the
--  Parent edge. Demo_Framing at the end is
--  what the change buys: two forests in two memories, where an operation on
--  one provably cannot disturb the other, and nothing has to be said about it.

procedure Union_Find_Separate with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type UF_Cell is record
      Parent : Plain_Handles.Handle;
      Size   : Positive;
   end record;

   package UF is new
     SPARK.Pointers.Explicit_Reclamation.Separate_Memory (UF_Cell);

   package UF_Copy is new UF.Copy_Operations;

   use UF;
   use UF_Copy;
   use Handle_Operations;
   use Memory_Model;

   function Cell_Parent (C : UF_Cell) return Pointer
   is (if Valid_Handle (C.Parent) then Of_Handle (C.Parent) else Null_Pointer)
   with Ghost => Static, Global => null;

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

   ---------------------------------------------------------------
   --  The model. Identical to the global-memory version: it was --
   --  already written over Memory_Map, not over the memory.     --
   ---------------------------------------------------------------

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
   --  It stays a named wrapper because the frame lemmas below attach to it
   --  with Automatic_Instantiation, and the two global conditions are a
   --  precondition rather than a conjunct so that a frame lemma can state
   --  Is_Rooted (M2, P).

   function Is_Rooted (M : Memory_Map; P : Pointer) return Boolean
   is (Reach.Is_Acyclic (P, M))
   with
     Ghost  => Static,
     Global => null,
     Pre    =>
       In_Memory (M, P)
       and then Reach.Valid_Memory (M)
       and then Valid_Handles (M);

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

   ------------------------------------------------------------------
   --  Operations. Every one is Global => null: the memory is now a --
   --  parameter, so the profile alone says what may be touched.    --
   ------------------------------------------------------------------

   procedure Make_Set (M : in out Memory_Type; P : out Pointer)
   with
     Global => SPARK.Pointers.Memory_Addresses,
     Pre    => Valid_Forest (+M),
     Post   =>
       Valid_Forest (+M)
       and then In_Memory (+M, P)
       and then Parent_Of (+M, P) = Null_Pointer
       and then Root_Of (+M, P) = P
       and then Deallocates (Memory_Map'(+M)'Old, +M, None);

   function Find (M : Memory_Type; P : Pointer) return Pointer
   with
     Global => null,
     Pre    => Valid_Forest (+M) and then In_Memory (+M, P),
     Post   => Find'Result = Root_Of (+M, P);

   function Set_Size (M : Memory_Type; P : Pointer) return Positive
   with
     Global => null,
     Pre    => Valid_Forest (+M) and then In_Memory (+M, P),
     Post   => Set_Size'Result = Size_Of (+M, Root_Of (+M, P));
   --  The size of P's set. Available because the size is stored on the side
   --  rather than being a property only of the model.

   procedure Union (M : in out Memory_Type; P, Q : Pointer)
   with
     Global => null,
     Pre    =>
       Valid_Forest (+M)
       and then In_Memory (+M, P)
       and then In_Memory (+M, Q)
       and then (if Root_Of (+M, P) /= Root_Of (+M, Q)
                 then Size_Of (+M, Root_Of (+M, P))
                      <= Natural'Last - Size_Of (+M, Root_Of (+M, Q))),
     Post   =>
       Valid_Forest (+M)
       and then Allocates (Memory_Map'(+M)'Old, +M, None)
       and then Deallocates (Memory_Map'(+M)'Old, +M, None)
       and then Root_Of (+M, P) = Root_Of (+M, Q)
       and then (for all A in Memory_Map'(+M)'Old =>
                   Root_Of (+M, A)
                   = (if Root_Of (Memory_Map'(+M)'Old, A)
                         = Root_Of (Memory_Map'(+M)'Old, P)
                      then Root_Of (+M, P)
                      elsif Root_Of (Memory_Map'(+M)'Old, A)
                            = Root_Of (Memory_Map'(+M)'Old, Q)
                      then Root_Of (+M, Q)
                      else Root_Of (Memory_Map'(+M)'Old, A)));

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

   procedure Make_Set (M : in out Memory_Type; P : out Pointer) is
   begin
      Create_Copy (M, (Parent => Null_Handle, Size => 1), P);
   end Make_Set;

   function Find (M : Memory_Type; P : Pointer) return Pointer is
      C : Pointer := P;
   begin
      while Of_Handle (Deref (M, C).Parent) /= Null_Pointer loop
         pragma Loop_Invariant (In_Memory (+M, C));
         pragma Loop_Invariant (Is_Rooted (+M, C));
         pragma Loop_Invariant (Root_Of (+M, C) = Root_Of (+M, P));
         pragma
           Loop_Variant
             (Decreases => Ptr_Sets.Length (Reach.Reachable_Set (C, +M)));
         C := Of_Handle (Deref (M, C).Parent);
      end loop;
      return C;
   end Find;

   function Set_Size (M : Memory_Type; P : Pointer) return Positive
   is (Deref (M, Find (M, P)).Size);

   procedure Union (M : in out Memory_Type; P, Q : Pointer) is
      RP : constant Pointer := Find (M, P);
      RQ : constant Pointer := Find (M, Q);
   begin
      if RP = RQ then
         return;
      end if;

      declare
         Size_P : constant Positive := Deref (M, RP).Size;
         Size_Q : constant Positive := Deref (M, RQ).Size;
      begin
         --  In both branches the new root's size is raised *before* the link.
         --  Linking first would leave an intermediate memory in which the
         --  child's size is not smaller than its parent's, breaking the
         --  invariant between two statements of the same operation.
         if Size_P < Size_Q then
            Assign
              (M, RQ,
               (Parent => Null_Handle, Size => Size_P + Size_Q));
            Assign (M, RP, (Parent => To_Handle (RQ), Size => Size_P));
         else
            Assign
              (M, RP,
               (Parent => Null_Handle, Size => Size_P + Size_Q));
            Assign (M, RQ, (Parent => To_Handle (RP), Size => Size_Q));
         end if;
      end;
   end Union;

   --------------------------------------------------------------------
   --  What separate memories buy. Union touches M1 only; the profile --
   --  says so, so everything known about M2 survives with no         --
   --  footprint contract, no lemma, and nothing said about M2 at all.--
   --------------------------------------------------------------------

   procedure Demo_Framing (M1, M2 : in out Memory_Type; P, Q, R : Pointer)
   with
     Global => null,
     Pre    =>
       Valid_Forest (+M1)
       and then In_Memory (+M1, P)
       and then In_Memory (+M1, Q)
       and then (if Root_Of (+M1, P) /= Root_Of (+M1, Q)
                 then Size_Of (+M1, Root_Of (+M1, P))
                      <= Natural'Last - Size_Of (+M1, Root_Of (+M1, Q)))
       and then Valid_Forest (+M2)
       and then In_Memory (+M2, R),
     Post   =>
       Valid_Forest (+M2)
       and then In_Memory (+M2, R)
       and then Root_Of (+M2, R) = Root_Of (Memory_Map'(+M2)'Old, R)
       and then Root_Of (+M1, P) = Root_Of (+M1, Q)
   is
   begin
      Union (M1, P, Q);
   end Demo_Framing;

begin
   null;
end Union_Find_Separate;
