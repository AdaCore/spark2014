with Interfaces; use Interfaces;
with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;
with Hidden_Pointers;

procedure Example_Recursive with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   package P1 is
      type Object is tagged null record;

      --  Lemma: Equality on Object is an equivalence.
      --  It will need to be proved for each new derivation
      function Witness (O : Object) return Big_Integer is (0);
      function "=" (O1, O2 : Object) return Boolean is
        (True)
      with Post'Class => "="'Result = (Witness (O1) = Witness (O2));
   end P1;
   use P1;

   package Pointers_To_Obj is new Hidden_Pointers (Object'Class);

   use Pointers_To_Obj;
   use Model;

   package Address_Conversions is new Signed_Conversions (Integer_64);
   use Address_Conversions;

   package P2 is
      type L_Cell is new Object with record
         V : Integer;
         N : Pointer;
      end record;

      --  Lemma: Equality on List is still an equivalence
      function Witness (O : L_Cell) return Big_Integer is
        (To_Big_Integer (O.V) * 2_147_483_648 + To_Big_Integer (Address (O.N)));
      function "=" (O1, O2 : L_Cell) return Boolean is
        (O1.V = O2.V and O1.N = O2.N);
   end P2;
   use P2;

   type List is record
      Length : Natural;
      Values : Pointer;
   end record;

   function Valid_List (L : Integer_64; N : Natural; M : Memory) return Boolean is
     (if L = 0 then N = 0
      else N /= 0
        and then Valid (M, L)
        and then Get (M, L) in L_Cell
        and then Valid_List (Address (L_Cell (Get (M, L)).N), N - 1, M))
   with Subprogram_Variant => (Decreases => N),
     Global => null,
     Ghost;
   -- L is an acyclic list of N elements

   --  Lemma:
   --    The acyclic list starting at L in M has a unique length
   procedure Prove_List_Unique_Length (L : Integer_64; N1, N2 : Natural; M : Memory) with
     Subprogram_Variant => (Decreases => N1),
     Ghost,
     Global => null,
     Pre => Valid_List (L, N1, M) and then Valid_List (L, N2, M),
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
     (Valid_List (Address (L.Values), L.Length, My_Memory))
   with Global => My_Memory,
     Ghost;

   function Reachable (L : Integer_64; N : Natural; A : Integer_64; M : Memory) return Boolean is
     (L /= 0 and then
        (L = A
         or else Reachable (Address (L_Cell (Get (M, L)).N), N - 1, A, M)))
   with Subprogram_Variant => (Decreases => N),
     Global => null,
     Ghost,
     Pre => Valid_List (L, N, M);
   --  A is reachable in the acyclic list starting at L in M

   --  Lemma:
   --    Reachable is a transitive relationship
   procedure Prove_Reach_Transitive (L1, L2, P : Integer_64; N1, N2 : Natural; M : Memory) with
     Subprogram_Variant => (Decreases => N1),
     Ghost,
     Global => null,
     Pre => Valid_List (L1, N1, M) and then Valid_List (L2, N2, M)
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
   procedure Prove_Valid_Preserved (L : Integer_64; N : Natural; M1, M2 : Memory) with
     Subprogram_Variant => (Decreases => N),
     Ghost,
     Global => null,
     Pre => Valid_List (L, N, M1)
     and then (for all A of M1 =>
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
   procedure Prove_Reach_Preserved (L : Integer_64; N : Natural; M1, M2 : Memory) with
     Subprogram_Variant => (Decreases => N),
     Ghost,
     Global => null,
     Pre => Valid_List (L, N, M1)
     and then (for all A of M1 =>
                 (if Reachable (L, N, A, M1)
                  then Valid (M2, A) and then Get (M1, A) = Get (M2, A))),
     Post => (for all A of M1 => Reachable (L, N, A, M1) = Reachable (L, N, A, M2))
   is
   begin
      if N /= 0 then
         Prove_Reach_Preserved (Address (L_Cell (Get (M1, L)).N), N - 1, M1, M2);
      end if;
      Prove_Valid_Preserved (L, N, M1, M2);
   end Prove_Reach_Preserved;

   --  Lemma:
   --    Appending two valid lists creates a valid list
   procedure Prove_Append_Valid (L1, L2, P : Integer_64; N1, N2 : Natural; M1, M2 : Memory) with
     Subprogram_Variant => (Decreases => N1),
     Ghost,
     Global => null,
     Pre => Valid_List (L1, N1, M1) and then Valid_List (L2, N2, M1)
     and then Reachable (L1, N1, P, M1)
     and then not Reachable (L2, N2, P, M1)
     and then Valid_List (P, 1, M1)
     and then (for all A of M1 => Valid (M2, A))
     and then (for all A of M2 => Valid (M1, A))
     and then (for all A of M1 =>
                 (if A /= P then Get (M1, A) = Get (M2, A)))
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
      end if;
   end Prove_Append_Valid;

   --  Lemma:
   --    The elements reachable from a list after an append are the elements
   --    reachable from either list before.
   procedure Prove_Append_Reach (L1, L2, P : Integer_64; N1, N2 : Natural; M1, M2 : Memory) with
     Subprogram_Variant => (Decreases => N1),
     Ghost,
     Global => null,
     Pre => Valid_List (L1, N1, M1) and then Valid_List (L2, N2, M1)
     and then Reachable (L1, N1, P, M1)
     and then not Reachable (L2, N2, P, M1)
     and then Valid_List (P, 1, M1)
     and then (for all A of M1 => Valid (M2, A))
     and then (for all A of M2 => Valid (M1, A))
     and then (for all A of M1 =>
                 (if A /= P then Get (M1, A) = Get (M2, A)))
     and then Get (M2, P) in L_Cell
     and then Address (L_Cell (Get (M2, P)).N) = L2
     and then Natural'Last - N1 >= N2,
     Post => (for all A of M1 => (Reachable (L1, N1, A, M1) or Reachable (L2, N2, A, M1)) =
                Reachable (L1, N1 + N2, A, M2))
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
     (for all A of My_Memory =>
        (if Reachable (Address (L1.Values), L1.Length, A, My_Memory)
         then not Reachable (Address (L2.Values), L2.Length, A, My_Memory)))
   with Global => My_Memory,
     Ghost,
     Pre => Valid_List (L1) and Valid_List (L2);

   --  Append a list at the end of another. We don't care about order or values
   --  here, just the list structure.
   procedure Append (L1 : in out List; L2 : List) with
     Global => (In_Out => My_Memory),
     --  L1 and L2 are valid list segments
     Pre => Valid_List (L1) and then Valid_List (L2)
     --  L1 and L2 are disjoint
     and then Disjoint (L1, L2)
     --  the sum of their lengthes is a natural
     and then Natural'Last - L1.Length >= L2.Length,

     --  L1 is a valid list segment
     Post => Valid_List (L1)
     --  It is long as L1 + L2
     and then L1.Length = L1.Length'Old + L2.Length'Old
     --  The rest of the memory is preserved
     and then (for all A of My_Memory => Valid (My_Memory'Old, A))
     and then (for all A of My_Memory'Old => Valid (My_Memory, A))
     and then (for all A of My_Memory'Old =>
                 (if not Reachable (Address (L1.Values)'Old, L1.Length'Old, A, My_Memory'Old)
                  then Get (My_Memory, A) = Get (My_Memory'Old, A)))
     --  The new list contains the same pointers as the 2 input lists
     and then (for all A of My_Memory => Reachable (Address (L1.Values), L1.Length, A, My_Memory) =
                 (Reachable (Address (L1.Values)'Old, L1.Length'Old, A, My_Memory'Old)
                  or else Reachable (Address (L2.Values), L2.Length, A, My_Memory'Old)))
   is
      My_Mem_Old : constant Memory := My_Memory with Ghost;
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
               pragma Loop_Invariant (Valid_List (Address (X), Max, My_Memory));
               pragma Loop_Invariant (Reachable (Address (L1.Values), L1.Length, Address (X), My_Memory));
               if L_Cell (Deref (X)).N = Null_Pointer then
                  declare
                     L : constant L_Cell := (L_Cell (Deref (X)) with delta N => L2.Values);
                  begin
                     Assign (X, Object'Class (L));
                     Prove_Append_Valid (Address (L1.Values), Address (L2.Values), Address (X), L1.Length, L2.Length, My_Mem_Old, My_Memory);
                     Prove_Append_Reach (Address (L1.Values), Address (L2.Values), Address (X), L1.Length, L2.Length, My_Mem_Old, My_Memory);
                     L1.Length := L1.Length + L2.Length;
                  end;
                  exit;
               end if;
               Prove_Reach_Transitive (Address (L1.Values), Address (X), Address (L_Cell (Deref (X)).N), L1.Length, Max, My_Memory);
               X := L_Cell (Deref (X)).N;
               Max := Max - 1;
            end loop;
         end;
      end if;
   end Append;

   L1 : List;
   L2 : List;
begin
   Create (L_Cell'(V => 3, N => Null_Pointer), L1.Values);
   Create (L_Cell'(V => 2, N => L1.Values), L1.Values);
   Create (L_Cell'(V => 1, N => L1.Values), L1.Values);
   L1.Length := 3;
   pragma Assert (Valid_List (L1));
   pragma Assert
     (for all A of My_Memory =>
        (if Reachable (Address (L1.Values), L1.Length, A, My_Memory)
         then A in Address (L1.Values) | Address (L_Cell (Deref (L1.Values)).N) | Address (L_Cell (Deref (L_Cell (Deref (L1.Values)).N)).N)));
   Create (L_Cell'(V => 6, N => Null_Pointer), L2.Values);
   Create (L_Cell'(V => 5, N => L2.Values), L2.Values);
   Create (L_Cell'(V => 4, N => L2.Values), L2.Values);
   L2.Length := 3;
   pragma Assert (Valid_List (L2));
   Append (L1, L2);
end Example_Recursive;
