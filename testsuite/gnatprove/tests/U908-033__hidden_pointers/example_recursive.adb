with Interfaces; use Interfaces;
with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;
with SPARK.Pointers.Explicit_Reclamation.Global_Memory;
with SPARK.Pointers.Handles.Plain_Handles; use SPARK.Pointers.Handles;

procedure Example_Recursive with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   --  Use an abstract handle to hold the pointer type in the recursive
   --  definition. As we use pointers with aliasing in a global memory model,
   --  the pointer type is not subject to ownership and we can use simple
   --  handles here.

   type L_Cell is record
      V : Natural;
      N : Plain_Handles.Handle;
   end record;

   function Is_Reclaimed (Unused : L_Cell) return Boolean is (True);
   package List_Pointers is new
     SPARK.Pointers.Explicit_Reclamation.Global_Memory (L_Cell, Is_Reclaimed);

   package List_Pointers_Copy_Operations is new List_Pointers.Copy_Operations;

   use List_Pointers;
   use List_Pointers_Copy_Operations;
   use Handle_Operations;
   use Memory_Model;

   function Eq (X, Y : L_Cell) return Boolean is
     (X.V = Y.V
      and then X.N = Y.N)
       with
   Pre => (Static => Valid_Handle (X.N) and Valid_Handle (Y.N));

   function Valid_Memory (M : Memory_Map) return Boolean is
     (for all A in M => Valid_Handle (Get (M, A).N)) with Ghost => Static;
   --  The memory only contains list cells

   type List is record
      Length : Natural;
      Values : Pointer;
   end record;

   --  This test reimplements reachability instead of using Abstract_Reachability
   --  which only works on acyclic lists.

   function Valid_List (L : Pointer; N : Natural; M : Memory_Map) return Boolean is
     (if L = Null_Pointer then N = 0
      else N /= 0
        and then In_Memory (M, L)
        and then Valid_List (Of_Handle (Get (M, L).N), N - 1, M))
   with Subprogram_Variant => (Decreases => N),
     Global => null,
     Pre => Valid_Memory (M),
     Ghost => Static;
   -- L is an acyclic list of N elements

   --  Lemma:
   --    The acyclic list starting at L in M has a unique length
   procedure Prove_List_Unique_Length (L : Pointer; N1, N2 : Natural; M : Memory_Map) with
     Subprogram_Variant => (Decreases => N1),
     Ghost => Static,
     Global => null,
     Pre => Valid_Memory (M) and then Valid_List (L, N1, M) and then Valid_List (L, N2, M),
     Post => N1 = N2
   is
   begin
      if L = Null_Pointer then
         return;
      else
         Prove_List_Unique_Length (Of_Handle (Get (M, L).N), N1 - 1, N2 - 1, M);
      end if;
   end Prove_List_Unique_Length;

   function Valid_List (L : List) return Boolean is
     (Valid_List (L.Values, L.Length, Model (Memory)))
   with Global => Memory,
     Pre => Valid_Memory (Model (Memory)),
     Ghost => Static;

   function Reachable (L : Pointer; N : Natural; A : Pointer; M : Memory_Map) return Boolean is
     (L /= Null_Pointer and then
        (L = A
         or else Reachable (Of_Handle (Get (M, L).N), N - 1, A, M)))
   with Subprogram_Variant => (Decreases => N),
     Global => null,
     Ghost => Static,
     Pre => Valid_Memory (M) and then Valid_List (L, N, M),
     Post => (if Reachable'Result then In_Memory (M, A));
   --  A is reachable in the acyclic list starting at L in M. Only valid cells
   --  are reachable, which is what lets the quantifications below range over
   --  a memory rather than over the whole pointer type.

   --  Lemma:
   --    Reachable is a transitive relationship
   procedure Prove_Reach_Transitive (L1, L2, P : Pointer; N1, N2 : Natural; M : Memory_Map) with
     Subprogram_Variant => (Decreases => N1),
     Ghost => Static,
     Global => null,
     Pre => Valid_Memory (M) and then Valid_List (L1, N1, M) and then Valid_List (L2, N2, M)
     and then Reachable (L1, N1, L2, M)
     and then Reachable (L2, N2, P, M),
     Post => Reachable (L1, N1, P, M)
   is
   begin
      if L1 = P then
         return;
      elsif L1 = L2 then
         Prove_List_Unique_Length (L1, N1, N2, M);
         return;
      else
         Prove_Reach_Transitive (Of_Handle (Get (M, L1).N), L2, P, N1 - 1, N2, M);
      end if;
   end Prove_Reach_Transitive;

   --  Lemma:
   --    Valid lists are preserved if the reachable elements are not modified
   procedure Prove_Valid_Preserved (L : Pointer; N : Natural; M1, M2 : Memory_Map) with
     Subprogram_Variant => (Decreases => N),
     Ghost => Static,
     Global => null,
     Pre => Valid_Memory (M1) and then Valid_Memory (M2) and then Valid_List (L, N, M1)
     and then (for all A in M1 =>
                 (if Reachable (L, N, A, M1)
                  then In_Memory (M2, A) and then Eq (Get (M1, A).all, Get (M2, A).all))),
     Post => Valid_List (L, N, M2)
   is
   begin
      if N = 0 then
         return;
      else
         Prove_Valid_Preserved (Of_Handle (Get (M1, L).N), N - 1, M1, M2);
      end if;
   end Prove_Valid_Preserved;

   --  Lemma:
   --    Reachability is preserved if the reachable elements are not modified
   procedure Prove_Reach_Preserved (L : Pointer; N : Natural; M1, M2 : Memory_Map) with
     Subprogram_Variant => (Decreases => N),
     Ghost => Static,
     Global => null,
     Pre => Valid_Memory (M1) and then Valid_Memory (M2) and then Valid_List (L, N, M1)
     and then (for all A in M1 =>
                 (if Reachable (L, N, A, M1)
                  then In_Memory (M2, A) and then Eq (Get (M1, A).all, Get (M2, A).all))),
     Post => (for all A in M2 => Reachable (L, N, A, M1) = Reachable (L, N, A, M2))
   is
   begin
      if N /= 0 then
         Prove_Reach_Preserved (Of_Handle (Get (M1, L).N), N - 1, M1, M2);
      end if;
      Prove_Valid_Preserved (L, N, M1, M2);
   end Prove_Reach_Preserved;

   --  Lemma:
   --    Appending two valid lists creates a valid list
   procedure Prove_Append_Valid (L1, L2, P : Pointer; N1, N2 : Natural; M1, M2 : Memory_Map) with
     Subprogram_Variant => (Decreases => N1),
     Ghost => Static,
     Global => null,
     Pre => Valid_Memory (M1) and then Valid_Memory (M2)
     and then Valid_List (L1, N1, M1) and then Valid_List (L2, N2, M1)
     and then Reachable (L1, N1, P, M1)
     and then not Reachable (L2, N2, P, M1)
     and then Valid_List (P, 1, M1)
     and then Allocates (M1, M2, None)
     and then Deallocates (M1, M2, None)
     and then Writes (M1, M2, Only (P))
     and then Of_Handle (Get (M2, P).N) = L2
     and then Natural'Last - N1 >= N2,
     Post => Valid_List (L1, N1 + N2, M2)
   is
   begin
      if N1 = 1 then
         Prove_Valid_Preserved (L2, N2, M1, M2);
      else
         Prove_Append_Valid (Of_Handle (Get (M1, L1).N), L2, P, N1 - 1, N2, M1, M2);
         pragma Assert (Valid_List (L1, N1 + N2, M2));
      end if;
   end Prove_Append_Valid;

   --  Lemma:
   --    The elements reachable from a list after an append are the elements
   --    reachable from either list before.
   procedure Prove_Append_Reach (L1, L2, P : Pointer; N1, N2 : Natural; M1, M2 : Memory_Map) with
     Subprogram_Variant => (Decreases => N1),
     Ghost => Static,
     Global => null,
     Pre => Valid_Memory (M1) and then Valid_Memory (M2)
     and then Valid_List (L1, N1, M1) and then Valid_List (L2, N2, M1)
     and then Reachable (L1, N1, P, M1)
     and then not Reachable (L2, N2, P, M1)
     and then Valid_List (P, 1, M1)
     and then Allocates (M1, M2, None)
     and then Deallocates (M1, M2, None)
     and then Writes (M1, M2, Only (P))
     and then Of_Handle (Get (M2, P).N) = L2
     and then Natural'Last - N1 >= N2,
     Post => (for all A in M2 => Reachable (L1, N1 + N2, A, M2) =
              (Reachable (L1, N1, A, M1) or Reachable (L2, N2, A, M1)))
   is
   begin
      if N1 = 1 then
         Prove_Reach_Preserved (L2, N2, M1, M2);
      else
         Prove_Append_Reach (Of_Handle (Get (M1, L1).N), L2, P, N1 - 1, N2, M1, M2);
      end if;
      Prove_Append_Valid (L1, L2, P, N1, N2, M1, M2);
   end Prove_Append_Reach;

   function Disjoint (L1, L2 : List) return Boolean is
     (for all A in Model (Memory) =>
        (if Reachable (L1.Values, L1.Length, A, Model (Memory))
         then not Reachable (L2.Values, L2.Length, A, Model (Memory))))
   with Global => Memory,
     Ghost => Static,
     Pre => Valid_Memory (Model (Memory)) and then Valid_List (L1) and then Valid_List (L2);

   --  A footprint cannot be built by comprehension over the pointer type the
   --  way it was over an address type: Elements is the only constructor for an
   --  arbitrary set, and its Choose parameter has to be a real subprogram. So
   --  the characterization stays in the contract and the body walks the list.

   function Walk (X : Pointer; K : Natural; Q : Pointer) return Boolean
   with
     Subprogram_Variant => (Decreases => K),
     Global => Memory,
     Pre  => Valid_Memory (Model (Memory))
             and then Valid_List (X, K, Model (Memory)),
     Post => Walk'Result = Reachable (X, K, Q, Model (Memory));
   --  Whether Q is reachable from X in K steps, computed rather than modelled

   function Reachable_Locations (A : Pointer; N : Natural) return Footprint
   with
     Global => Memory,
     Pre  => Valid_Memory (Model (Memory))
             and then Valid_List (A, N, Model (Memory)),
     Post => (for all Q in Reachable_Locations'Result =>
                Reachable (A, N, Q, Model (Memory)))
             and then
               (for all Q in Model (Memory) =>
                  (if Reachable (A, N, Q, Model (Memory))
                   then Contains (Reachable_Locations'Result, Q)));
   --  All locations reachable from A in the current memory. Both directions
   --  are needed here: the lemma that gives Reachable -> Contains is attached
   --  to Elements, so it is only instantiated in the body below, not at the
   --  places where the result of this function is used as a footprint.

   function Reachable_Locations (L : List) return Footprint is
     (Reachable_Locations (L.Values, L.Length))
   with Global => Memory,
     Pre => Valid_Memory (Model (Memory)) and then Valid_List (L),
     Annotate => (GNATprove, Inline_For_Proof);
   --  All locations reachable through L

   function Walk (X : Pointer; K : Natural; Q : Pointer) return Boolean is
   begin
      if X = Null_Pointer then
         return False;
      elsif X = Q then
         return True;
      else
         return Walk (Of_Handle (Constant_Reference (Memory, X).N), K - 1, Q);
      end if;
   end Walk;

   function Reachable_Locations (A : Pointer; N : Natural) return Footprint is

      function Is_Reach (Q : Pointer) return Boolean
      with
        Global => (Input => (Memory, A, N)),
        Pre  => Valid_Memory (Model (Memory))
                and then Valid_List (A, N, Model (Memory)),
        Post => Is_Reach'Result = Reachable (A, N, Q, Model (Memory));

      function Is_Reach (Q : Pointer) return Boolean is (Walk (A, N, Q));

   begin
      return Elements (Is_Reach'Access);
   end Reachable_Locations;

   --  Append a list at the end of another. We don't care about order or values
   --  here, just the list structure.
   procedure Append (L1 : in out List; L2 : List) with
     Global => (In_Out => Memory),
     Pre => Valid_Memory (Model (Memory))
     --  L1 and L2 are valid lists
     and then Valid_List (L1) and then Valid_List (L2)
     --  L1 and L2 are disjoint
     and then Disjoint (L1, L2)
     --  the sum of their lengths is a natural
     and then Natural'Last - L1.Length >= L2.Length,

     Post => Valid_Memory (Model (Memory))
     --  L1 is a valid list
     and then Valid_List (L1)
     --  It is long as L1 + L2
     and then L1.Length = L1.Length'Old + L2.Length'Old
     --  The new list contains the same pointers as the 2 input lists
     and then (for all A in Model (Memory) => Reachable (L1.Values, L1.Length, A, Model (Memory)) =
                 (Reachable (L1.Values'Old, L1.Length'Old, A, Model (Memory)'Old)
                  or Reachable (L2.Values, L2.Length, A, Model (Memory)'Old)))
     --  Nothing has been allocated or deallocated
     and then Allocates (Model (Memory)'Old, Model (Memory), None)
     and then Deallocates (Model (Memory)'Old, Model (Memory), None)
     --  Only cells reachable from L1 before the call have been modified
     and then Writes (Model (Memory)'Old, Model (Memory), Reachable_Locations (L1)'Old)
   is
      Mem_Old : constant Memory_Map := Model (Memory) with Ghost => Static;
   begin
      if L1.Length = 0 then
         L1 := L2;
      elsif L2.Length = 0 then
         return;
      else
         declare
            X   : Pointer := L1.Values;
            Max : Natural := L1.Length with Ghost;
         begin
            loop
               pragma Loop_Invariant (X /= Null_Pointer);
               pragma Loop_Invariant (Valid_List (X, Max, Model (Memory)));
               pragma Loop_Invariant (Reachable (L1.Values, L1.Length, X, Model (Memory)));

               --  Use Constant_Reference to convert X into an ownership
               --  pointer so its designated value is not copied.

               if Of_Handle (Constant_Reference (Memory, X).N) = Null_Pointer then

                  --  Use Reference to convert X into an ownership pointer so
                  --  its designated value can be updated in place.

                  declare
                     X_Ptr : access L_Cell := Reference (Memory, X);
                  begin
                     X_Ptr.N := To_Handle (L2.Values);
                  end;
                  Prove_Append_Valid (L1.Values, L2.Values, X, L1.Length, L2.Length, Mem_Old, Model (Memory));
                  Prove_Append_Reach (L1.Values, L2.Values, X, L1.Length, L2.Length, Mem_Old, Model (Memory));
                  L1.Length := L1.Length + L2.Length;
                  exit;
               end if;
               Prove_Reach_Transitive (L1.Values, X, Of_Handle (Deref (X).N), L1.Length, Max, Model (Memory));
               X := Of_Handle (Constant_Reference (Memory, X).N);
               Max := Max - 1;
            end loop;
         end;
      end if;
   end Append;

   type Nat_Array is array (Positive range <>) of Natural;
   procedure Create_List (Values : Nat_Array; L : out List) with
     Pre => Valid_Memory (Model (Memory)),
     Post => Valid_Memory (Model (Memory))
     and L.Length = Values'Length
     and Valid_List (L)
     and Allocates (Model (Memory)'Old, Model (Memory), Reachable_Locations (L))
     and Deallocates (Model (Memory)'Old, Model (Memory), None)
     and Writes (Model (Memory)'Old, Model (Memory), None)
   is
      M : Memory_Map with Ghost => Static;
   begin
      L.Values := Null_Pointer;
      for I in reverse Values'Range loop
         M := Model (Memory);
         List_Pointers_Copy_Operations.Create_Copy
           (L_Cell'(V => Values (I), N => To_Handle (L.Values)), L.Values);
         Prove_Valid_Preserved
           (Of_Handle (Deref (L.Values).N), Values'Last - I, M, Model (Memory));
         Prove_Reach_Preserved
           (Of_Handle (Deref (L.Values).N), Values'Last - I, M, Model (Memory));
         pragma Loop_Invariant (Valid_Memory (Model (Memory)));
         pragma Loop_Invariant
           (Valid_List (L.Values, Values'Last - I + 1, Model (Memory)));
         pragma Loop_Invariant
           (Allocates (Model (Memory)'Loop_Entry, Model (Memory),
            Reachable_Locations (L.Values, Values'Last - I + 1)));
         pragma Loop_Invariant
           (Deallocates (Model (Memory)'Loop_Entry, Model (Memory), None));
         pragma Loop_Invariant
           (Writes (Model (Memory)'Loop_Entry, Model (Memory), None));
      end loop;
      L.Length := Values'Length;
   end Create_List;

   function Rand (X : Integer) return Boolean with Import;

   procedure Test with Pre => Valid_Memory (Model (Memory)) is
      L1 : List;
      L2 : List;
      L3 : List;
      M  : Memory_Map with Ghost => Static;
   begin
      Create_List ((1, 2, 3), L1);
      Create_List ((4, 5, 6), L2);
      Create_List ((7, 8, 9), L3);
      pragma Assert (Valid_List (L1));
      pragma Assert (Valid_List (L2));
      pragma Assert (Valid_List (L3));
      pragma Assert (Disjoint (L1, L2));
      pragma Assert (Disjoint (L2, L3));
      pragma Assert (Disjoint (L1, L3));

      M := Model (Memory);
      Append (L1, L2);
      Prove_Valid_Preserved (L2.Values, L2.Length, M, Model (Memory));
      Prove_Reach_Preserved (L2.Values, L2.Length, M, Model (Memory));
      Prove_Valid_Preserved (L3.Values, L3.Length, M, Model (Memory));
      Prove_Reach_Preserved (L3.Values, L3.Length, M, Model (Memory));

      if Rand (0) then
         Append (L1, L3);
         pragma Assert (Valid_List (L2)); --  Not provable, L2 has been silently updated in an unknown way
      elsif Rand (1) then
         M := Model (Memory);
         Append (L3, L2);
         Prove_Valid_Preserved (L1.Values, L1.Length, M, Model (Memory));
         pragma Assert (Valid_List (L1)); --  Ok, L1 and L3 are valid lists sharing the same tail
      elsif Rand (2) then
         Append (L1, L2); --  The call is not allowed, L1 and L2 are not disjoint, it would cause a cycle
      end if;
   end Test;
begin
   null;
end Example_Recursive;
