with Interfaces; use Interfaces;
with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;
with Pointers_With_Aliasing;

procedure Example_Recursive with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Object is tagged null record;

   package Pointers_To_Obj is new Pointers_With_Aliasing (Object'Class);

   use Pointers_To_Obj;
   use Memory_Model;

   type L_Cell is new Object with record
      V : Natural;
      N : Pointer;
   end record;

   function Valid_Memory (M : Memory_Type) return Boolean is
     (for all A in M => Get (M, A) in L_Cell);
   --  The memory only contains list cells. It is important because the
   --  modelisation of the memory is based on "=" on Object, so we need to
   --  know what it is.

   type List is record
      Length : Natural;
      Values : Pointer;
   end record;

   function Valid_List (L : Address_Type; N : Natural; M : Memory_Type) return Boolean is
     (if L = 0 then N = 0
      else N /= 0
        and then Valid (M, L)
        and then Valid_List (Address (L_Cell (Get (M, L)).N), N - 1, M))
   with Subprogram_Variant => (Decreases => N),
     Global => null,
     Pre => Valid_Memory (M),
     Ghost;
   -- L is an acyclic list of N elements

   --  Lemma:
   --    The acyclic list starting at L in M has a unique length
   procedure Prove_List_Unique_Length (L : Address_Type; N1, N2 : Natural; M : Memory_Type) with
     Subprogram_Variant => (Decreases => N1),
     Ghost,
     Global => null,
     Pre => Valid_Memory (M) and then Valid_List (L, N1, M) and then Valid_List (L, N2, M),
     Post => N1 = N2
   is
   begin
      if L = 0 then
         return;
      else
         Prove_List_Unique_Length (Address (L_Cell (Get (M, L)).N), N1 - 1, N2 - 1, M);
      end if;
   end Prove_List_Unique_Length;

   function Valid_List (L : List) return Boolean is
     (Valid_List (Address (L.Values), L.Length, Memory))
   with Global => Memory,
     Pre => Valid_Memory (Memory),
     Ghost;

   function Reachable (L : Address_Type; N : Natural; A : Address_Type; M : Memory_Type) return Boolean is
     (L /= 0 and then
        (L = A
         or else Reachable (Address (L_Cell (Get (M, L)).N), N - 1, A, M)))
   with Subprogram_Variant => (Decreases => N),
     Global => null,
     Ghost,
     Pre => Valid_Memory (M) and then Valid_List (L, N, M);
   --  A is reachable in the acyclic list starting at L in M

   --  Lemma:
   --    Reachable is a transitive relationship
   procedure Prove_Reach_Transitive (L1, L2, P : Address_Type; N1, N2 : Natural; M : Memory_Type) with
     Subprogram_Variant => (Decreases => N1),
     Ghost,
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
         Prove_Reach_Transitive (Address (L_Cell (Get (M, L1)).N), L2, P, N1 - 1, N2, M);
      end if;
   end Prove_Reach_Transitive;

   --  Lemma:
   --    Valid lists are preserved if the reachable elements are not modified
   procedure Prove_Valid_Preserved (L : Address_Type; N : Natural; M1, M2 : Memory_Type) with
     Subprogram_Variant => (Decreases => N),
     Ghost,
     Global => null,
     Pre => Valid_Memory (M1) and then Valid_Memory (M2) and then Valid_List (L, N, M1)
     and then (for all A in M1 =>
                 (if Reachable (L, N, A, M1)
                  then Valid (M2, A) and then Get (M1, A) = Get (M2, A))),
     Post => Valid_List (L, N, M2)
   is
   begin
      if N = 0 then
         return;
      else
         Prove_Valid_Preserved (Address (L_Cell (Get (M1, L)).N), N - 1, M1, M2);
      end if;
   end Prove_Valid_Preserved;

   --  Lemma:
   --    Reachability is preserved if the reachable elements are not modified
   procedure Prove_Reach_Preserved (L : Address_Type; N : Natural; M1, M2 : Memory_Type) with
     Subprogram_Variant => (Decreases => N),
     Ghost,
     Global => null,
     Pre => Valid_Memory (M1) and then Valid_Memory (M2) and then Valid_List (L, N, M1)
     and then (for all A in M1 =>
                 (if Reachable (L, N, A, M1)
                  then Valid (M2, A) and then Get (M1, A) = Get (M2, A))),
     Post => (for all A in Address_Type => Reachable (L, N, A, M1) = Reachable (L, N, A, M2))
   is
   begin
      if N /= 0 then
         Prove_Reach_Preserved (Address (L_Cell (Get (M1, L)).N), N - 1, M1, M2);
      end if;
      Prove_Valid_Preserved (L, N, M1, M2);
   end Prove_Reach_Preserved;

   --  Lemma:
   --    Appending two valid lists creates a valid list
   procedure Prove_Append_Valid (L1, L2, P : Address_Type; N1, N2 : Natural; M1, M2 : Memory_Type) with
     Subprogram_Variant => (Decreases => N1),
     Ghost,
     Global => null,
     Pre => Valid_Memory (M1) and then Valid_Memory (M2)
     and then Valid_List (L1, N1, M1) and then Valid_List (L2, N2, M1)
     and then Reachable (L1, N1, P, M1)
     and then not Reachable (L2, N2, P, M1)
     and then Valid_List (P, 1, M1)
     and then Allocates (M1, M2, None)
     and then Deallocates (M1, M2, None)
     and then Writes (M1, M2, Only (P))
     and then Get (M2, P) in L_Cell
     and then Address (L_Cell (Get (M2, P)).N) = L2
     and then Natural'Last - N1 >= N2,
     Post => Valid_List (L1, N1 + N2, M2)
   is
   begin
      if N1 = 1 then
         Prove_Valid_Preserved (L2, N2, M1, M2);
      else
         Prove_Append_Valid (Address (L_Cell (Get (M1, L1)).N), L2, P, N1 - 1, N2, M1, M2);
         pragma Assert (Valid_List (L1, N1 + N2, M2));
      end if;
   end Prove_Append_Valid;

   --  Lemma:
   --    The elements reachable from a list after an append are the elements
   --    reachable from either list before.
   procedure Prove_Append_Reach (L1, L2, P : Address_Type; N1, N2 : Natural; M1, M2 : Memory_Type) with
     Subprogram_Variant => (Decreases => N1),
     Ghost,
     Global => null,
     Pre => Valid_Memory (M1) and then Valid_Memory (M2)
     and then Valid_List (L1, N1, M1) and then Valid_List (L2, N2, M1)
     and then Reachable (L1, N1, P, M1)
     and then not Reachable (L2, N2, P, M1)
     and then Valid_List (P, 1, M1)
     and then Allocates (M1, M2, None)
     and then Deallocates (M1, M2, None)
     and then Writes (M1, M2, Only (P))
     and then Get (M2, P) in L_Cell
     and then Address (L_Cell (Get (M2, P)).N) = L2
     and then Natural'Last - N1 >= N2,
     Post => (for all A in Address_Type => Reachable (L1, N1 + N2, A, M2) =
              (Reachable (L1, N1, A, M1) or Reachable (L2, N2, A, M1)))
   is
   begin
      if N1 = 1 then
         Prove_Reach_Preserved (L2, N2, M1, M2);
      else
         Prove_Append_Reach (Address (L_Cell (Get (M1, L1)).N), L2, P, N1 - 1, N2, M1, M2);
      end if;
      Prove_Append_Valid (L1, L2, P, N1, N2, M1, M2);
   end Prove_Append_Reach;

   function Disjoint (L1, L2 : List) return Boolean is
     (for all A in Address_Type =>
        (if Reachable (Address (L1.Values), L1.Length, A, Memory)
         then not Reachable (Address (L2.Values), L2.Length, A, Memory)))
   with Global => Memory,
     Ghost,
     Pre => Valid_Memory (Memory) and then Valid_List (L1) and then Valid_List (L2);

   function Reachable_Locations (A : Address_Type; N : Natural; M : Memory_Type) return Addresses is
     ([for Q in Address_Type => Reachable (A, N, Q, M)])
   with Ghost,
     Pre => Valid_Memory (M) and then Valid_List (A, N, M),
     Annotate => (GNATprove, Inline_For_Proof);
   --  All locations reachable from A in M

   function Reachable_Locations (L : List) return Addresses is
     (Reachable_Locations (Address (L.Values), L.Length, Memory))
   with Ghost,
     Pre => Valid_Memory (Memory) and then Valid_List (L),
     Annotate => (GNATprove, Inline_For_Proof);
   --  All locations reachable through L

   --  Append a list at the end of another. We don't care about order or values
   --  here, just the list structure.
   procedure Append (L1 : in out List; L2 : List) with
     Global => (In_Out => Memory),
     Pre => Valid_Memory (Memory)
     --  L1 and L2 are valid lists
     and then Valid_List (L1) and then Valid_List (L2)
     --  L1 and L2 are disjoint
     and then Disjoint (L1, L2)
     --  the sum of their lengths is a natural
     and then Natural'Last - L1.Length >= L2.Length,

     Post => Valid_Memory (Memory)
     --  L1 is a valid list
     and then Valid_List (L1)
     --  It is long as L1 + L2
     and then L1.Length = L1.Length'Old + L2.Length'Old
     --  The new list contains the same pointers as the 2 input lists
     and then (for all A in Address_Type => Reachable (Address (L1.Values), L1.Length, A, Memory) =
                 (Reachable (Address (L1.Values)'Old, L1.Length'Old, A, Memory'Old)
                  or Reachable (Address (L2.Values), L2.Length, A, Memory'Old)))
     --  Nothing has been allocated or deallocated
     and then Allocates (Memory'Old, Memory, None)
     and then Deallocates (Memory'Old, Memory, None)
     --  Only cells reachable from L1 before the call have been modified
     and then Writes (Memory'Old, Memory, Reachable_Locations (L1)'Old)
   is
      Mem_Old : constant Memory_Type := Memory with Ghost;
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
               pragma Loop_Invariant (Valid_List (Address (X), Max, Memory));
               pragma Loop_Invariant (Reachable (Address (L1.Values), L1.Length, Address (X), Memory));

               --  Use Constant_Reference to convert X into an ownership
               --  pointer so its designated value is not copied.

               if L_Cell (Constant_Reference (Memory, X).all).N = Null_Pointer then

                  --  Use Reference to convert X into an ownership pointer so
                  --  its designated value can be updated in place.

                  declare
                     Mem_Access : access Memory_Type := Memory'Access;
                     X_Ptr      : access Object'Class := Reference (Mem_Access, X);
                  begin
                     L_Cell (X_Ptr.all).N := L2.Values;
                  end;
                  Prove_Append_Valid (Address (L1.Values), Address (L2.Values), Address (X), L1.Length, L2.Length, Mem_Old, Memory);
                  Prove_Append_Reach (Address (L1.Values), Address (L2.Values), Address (X), L1.Length, L2.Length, Mem_Old, Memory);
                  L1.Length := L1.Length + L2.Length;
                  exit;
               end if;
               Prove_Reach_Transitive (Address (L1.Values), Address (X), Address (L_Cell (Deref (X)).N), L1.Length, Max, Memory);
               X := L_Cell (Constant_Reference (Memory, X).all).N;
               Max := Max - 1;
            end loop;
         end;
      end if;
   end Append;

   type Nat_Array is array (Positive range <>) of Natural;
   procedure Create_List (Values : Nat_Array; L : out List) with
     Pre => Valid_Memory (Memory),
     Post => Valid_Memory (Memory)
     and L.Length = Values'Length
     and Valid_List (L)
     and Allocates (Memory'Old, Memory, Reachable_Locations (L))
     and Deallocates (Memory'Old, Memory, None)
     and Writes (Memory'Old, Memory, None)
   is
      M : Memory_Type with Ghost;
   begin
      L.Values := Null_Pointer;
      for I in reverse Values'Range loop
         M := Memory;
         Create (L_Cell'(V => Values (I), N => L.Values), L.Values);
         Prove_Valid_Preserved
           (Address (L_Cell (Deref (L.Values)).N), Values'Last - I, M, Memory);
         Prove_Reach_Preserved
           (Address (L_Cell (Deref (L.Values)).N), Values'Last - I, M, Memory);
         pragma Loop_Invariant (Valid_Memory (Memory));
         pragma Loop_Invariant
           (Valid_List (Address (L.Values), Values'Last - I + 1, Memory));
         pragma Loop_Invariant
           (Allocates (Memory'Loop_Entry, Memory,
            Reachable_Locations (Address (L.Values), Values'Last - I + 1, Memory)));
         pragma Loop_Invariant
           (Deallocates (Memory'Loop_Entry, Memory, None));
         pragma Loop_Invariant
           (Writes (Memory'Loop_Entry, Memory, None));
      end loop;
      L.Length := Values'Length;
   end Create_List;

   function Rand (X : Integer) return Boolean with Import;

   L1 : List;
   L2 : List;
   L3 : List;
   M  : Memory_Type with Ghost;
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

   M := Memory;
   Append (L1, L2);
   Prove_Valid_Preserved (Address (L2.Values), L2.Length, M, Memory);
   Prove_Reach_Preserved (Address (L2.Values), L2.Length, M, Memory);
   Prove_Valid_Preserved (Address (L3.Values), L3.Length, M, Memory);
   Prove_Reach_Preserved (Address (L3.Values), L3.Length, M, Memory);

   if Rand (0) then
      Append (L1, L3);
      pragma Assert (Valid_List (L2)); --  Not provable, L2 has been silently updated in an unknown way
   elsif Rand (1) then
      M := Memory;
      Append (L3, L2);
      Prove_Valid_Preserved (Address (L1.Values), L1.Length, M, Memory);
      pragma Assert (Valid_List (L1)); --  Ok, L1 and L3 are valid lists sharing the same tail
   elsif Rand (2) then
      Append (L1, L2); --  The call is not allowed, L1 and L2 are not disjoint, it would cause a cycle
   end if;
end Example_Recursive;
