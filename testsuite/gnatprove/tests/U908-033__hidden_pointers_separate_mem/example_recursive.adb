with Interfaces;              use Interfaces;
with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with SPARK.Pointers.Pointers_With_Aliasing_Separate_Memory;

procedure Example_Recursive with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   type Object is tagged null record;

   package Pointers_To_Obj is new SPARK.Pointers.Pointers_With_Aliasing_Separate_Memory (Object'Class);

   use Pointers_To_Obj;
   use Memory_Model;

   type L_Cell is new Object with record
      V : Natural;
      N : Pointer;
   end record;

   function Valid_Memory (M : Memory_Map) return Boolean is
     (for all A in M => Get (M, A) in L_Cell);
   --  The memory only contains list cells. It is important because the
   --  modelisation of the memory is based on "=" on Object, so we need to
   --  know what it is.

   type List is record
      M : aliased Memory_Type;
      F : Pointer;
      L : Positive;
   end record;

   function Valid_List (F, A : Address_Type; L : Positive; M : Memory_Map) return Boolean is
     (F /= 0 and then A /= 0 and then Valid (M, F) and then Valid (M, A) and then
        (if L = 1 then Address (L_Cell (Get (M, A)).N) = F
         else Address (L_Cell (Get (M, A)).N) /= F
         and then Valid_List (F, Address (L_Cell (Get (M, A)).N), L - 1, M)))
   with Subprogram_Variant => (Decreases => L),
     Global => null,
     Pre => Valid_Memory (M),
     Ghost;

   function Valid_List (L : List) return Boolean is
     (Valid_Memory (+L.M)
      and then Valid_List (Address (L.F), Address (L.F), L.L, +L.M))
   with Ghost;
   -- L is a cyclic list

   function Reachable (F, A1 : Address_Type; L : Positive; A2 : Address_Type; M : Memory_Map) return Boolean is
     (A1 = A2
      or else (L > 1 and then Reachable (F, Address (L_Cell (Get (M, A1)).N), L - 1, A2, M)))
   with Subprogram_Variant => (Decreases => L),
     Global => null,
     Ghost,
     Pre  => Valid_Memory (M) and then Valid_List (F, A1, L, M),
     Post => (if Reachable'Result then Valid (M, A2));
   --  A is reachable in a cyclic list

   function Valid_List_No_Leak (L : List) return Boolean is
     (Valid_List (L)
      and then (for all A in +L.M =>
                     Reachable (Address (L.F), Address (L.F), L.L, A, +L.M)))
   with Ghost;
   --  All cells of L.M are reachable from L.F

   --  Lemma:
   --    Valid lists are preserved if the reachable elements are not modified
   procedure Prove_Valid_Preserved (F, A : Address_Type; L : Positive; M1, M2 : Memory_Map) with
     Subprogram_Variant => (Decreases => L),
     Ghost,
     Global => null,
     Pre => Valid_Memory (M1) and then Valid_Memory (M2) and then Valid_List (F, A, L, M1)
     and then Valid (M2, F)
     and then (for all A2 in M1 =>
                 (if Reachable (F, A, L, A2, M1) and then (F = A or A2 /= F)
                  then Valid (M2, A2) and then Get (M1, A2) = Get (M2, A2))),
     Post => Valid_List (F, A, L, M2)
   is
   begin
      if L = 1 then
         return;
      elsif F /= A and L = 2 then
         return;
      else
         Prove_Valid_Preserved (F, Address (L_Cell (Get (M1, A)).N), L - 1, M1, M2);
         pragma Assert (Valid_List (F, A, L, M2));
      end if;
   end Prove_Valid_Preserved;

   --  Lemma:
   --    Reachability is preserved if the reachable elements are not modified
   procedure Prove_Reach_Preserved (F, A : Address_Type; L : Positive; M1, M2 : Memory_Map) with
     Subprogram_Variant => (Decreases => L),
     Ghost,
     Global => null,
     Pre => Valid_Memory (M1) and then Valid_Memory (M2) and then Valid_List (F, A, L, M1)
     and then Valid (M2, F)
     and then (for all A2 in M1 =>
                 (if Reachable (F, A, L, A2, M1) and then (F = A or A2 /= F)
                  then Valid (M2, A2) and then Get (M1, A2) = Get (M2, A2))),
     Post => (for all A2 in Address_Type => Reachable (F, A, L, A2, M1) = Reachable (F, A, L, A2, M2))
   is
   begin
      if L = 1 then
         return;
      elsif L > 2 then
         Prove_Reach_Preserved (F, Address (L_Cell (Get (M1, A)).N), L - 1, M1, M2);
      end if;
      Prove_Valid_Preserved (F, A, L, M1, M2);
   end Prove_Reach_Preserved;

   --  Lemma:
   --    Concatenating two valid list segments creates a valid list segment
   procedure Prove_Valid_Concat
     (F1, A1 : Address_Type; L1 : Positive;
      F2, A2 : Address_Type; L2 : Natural; M : Memory_Map)
   with
     Subprogram_Variant => (Decreases => L1),
     Ghost,
     Global => null,
     Pre => Valid_Memory (M)
       and then L1 < Positive'Last - L2
       and then Valid_List (F1, A1, L1, M)
       and then (if L2 = 0 then F2 = A2 and then Valid (M, F2)
                 else F2 /= A2 and then Valid_List (F2, A2, L2, M))
       and then not Reachable (F1, A1, L1, F2, M)
       and then F1 /= F2
       and then Address (L_Cell (Get (M, F1)).N) = A2,
     Post => Valid_List (F2, A1, L1 + L2 + 1, M)
   is
   begin
      if L1 = 1 then
         return;
      else
         Prove_Valid_Concat (F1, Address (L_Cell (Get (M, A1)).N), L1 - 1, F2, A2, L2, M);
      end if;
   end Prove_Valid_Concat;

   --  Lemma:
   --    The elements reachable in the concatenation of two valid list segments
   --    are the elements reachable in each segments plus the middle one.
   procedure Prove_Reach_Concat
     (F1, A1 : Address_Type; L1 : Positive;
      F2, A2 : Address_Type; L2 : Natural; M : Memory_Map)
   with
     Subprogram_Variant => (Decreases => L1),
     Ghost,
     Global => null,
     Pre => Valid_Memory (M)
       and then L1 < Positive'Last - L2
       and then Valid_List (F1, A1, L1, M)
       and then (if L2 = 0 then F2 = A2 and then Valid (M, F2)
                 else F2 /= A2 and then Valid_List (F2, A2, L2, M))
       and then not Reachable (F1, A1, L1, F2, M)
       and then F1 /= F2
       and then Address (L_Cell (Get (M, F1)).N) = A2,
     Post => (for all B in M => Reachable (F2, A1, L1 + L2 + 1, B, M) =
                (Reachable (F1, A1, L1, B, M) or B = F1
                 or (L2 > 0 and then Reachable (F2, A2, L2, B, M))))
   is
   begin
      if L1 = 1 then
         return;
      else
         Prove_Reach_Concat (F1, Address (L_Cell (Get (M, A1)).N), L1 - 1, F2, A2, L2, M);
         Prove_Valid_Concat (F1, Address (L_Cell (Get (M, A1)).N), L1 - 1, F2, A2, L2, M);
      end if;
   end Prove_Reach_Concat;

   function Get (F, A : Address_Type; P, L : Positive; M : Memory_Map) return Natural is
     (if P = 1 then L_Cell (Get (M, A)).V
      else Get (F, Address (L_Cell (Get (M, A)).N), P - 1, L - 1, M))
   with Subprogram_Variant => (Decreases => L),
     Global => null,
     Pre => Valid_Memory (M) and then Valid (M, F)
     and then Valid_List (F, A, L, M) and then P <= L,
     Ghost;

   function Get (L : List; P : Positive) return Natural is
     (Get (Address (L.F), Address (L.F), P, L.L, +L.M))
   with
     Global => null,
     Pre => Valid_List (L) and then P <= L.L,
     Ghost;

   --  Create a cyclic list containing a single cell
   function Create (V : Natural) return List with
     Post => Valid_List_No_Leak (Create'Result)
     and then Create'Result.L = 1
     and then Get (Create'Result, 1) = V;

   function Create (V : Natural) return List is
      M : aliased Memory_Type := Empty_Map;
      F : Pointer;
   begin
      Create (M, L_Cell'(V, Null_Pointer), F);

      --  Use Reference to convert F into an ownership pointer so
      --  its designated value can be updated in place.

      declare
         Mem_Access : access Memory_Type := M'Access;
      begin
         declare
            F_Ptr      : access Object'Class := Reference (Mem_Access, F);
         begin
            L_Cell (F_Ptr.all).N := F;
         end;
      end;

      pragma Assert (Valid_Memory (+M));
      pragma Assert (L_Cell (Get (+M, Address (F))).N = F);

      return (M => M, F => F, L => 1);
   end Create;

   --  Insert a value in a cyclic list
   procedure Add (L : in out List; V : Natural) with
     Pre  => Valid_List_No_Leak (L) and then L.L < Natural'Last,
     Post => Valid_List_No_Leak (L) and then L.L = L.L'Old + 1;

   procedure Add (L : in out List; V : Natural) is
      F_Next : Pointer := L_Cell (Deref (L.M, L.F)).N;
      New_P  : Pointer;
      M_Old  : constant Memory_Map := +L.M with Ghost;
   begin
      Create (L.M, L_Cell'(V, F_Next), New_P);
      pragma Assert (Valid_Memory (+L.M));

      --  Use Reference to convert L.F into an ownership pointer so
      --  its designated value can be updated in place.

      declare
         Mem_Access : access Memory_Type := L.M'Access;
         F_Ptr      : access Object'Class := Reference (Mem_Access, L.F);
      begin
         L_Cell (F_Ptr.all).N := New_P;
      end;

      pragma Assert (Valid_Memory (+L.M));
      pragma Assert (L_Cell (Get (+L.M, Address (L.F))).N = New_P);
      pragma Assert (L_Cell (Get (+L.M, Address (New_P))).N = F_Next);

      if L.L > 1 then
         Prove_Valid_Preserved (Address (L.F), Address (F_Next), L.L - 1, M_Old, +L.M);
         Prove_Reach_Preserved (Address (L.F), Address (F_Next), L.L - 1, M_Old, +L.M);
      end if;

      L.L := L.L + 1;
   end Add;

   --  Merge 2 cyclic lists
   procedure Merge (L1, L2 : in out List) with
     Pre  => Valid_List_No_Leak (L1) and then Valid_List_No_Leak (L2)
     and then L1.L <= Natural'Last - L2.L,
     Post => Valid_List_No_Leak (L1) and then Is_Empty (L2.M)
     and then L1.L = L1.L'Old + L2.L'Old;

   procedure Merge (L1, L2 : in out List) is
      function Valid_In_L2 (A : Address_Type) return Boolean is
        (Valid (+L2.M, A));

      F1_Next : Pointer;
      F2_Next : Pointer;
      M1_Old  : constant Memory_Map := +L1.M with Ghost;
      M2_Old  : constant Memory_Map := +L2.M with Ghost;
      M_Old   : Memory_Map with Ghost;
   begin
      Move_Memory (L2.M, L1.M, Elements (Valid_In_L2'Access));
      pragma Assert (Valid_Memory (+L1.M));

      Prove_Valid_Preserved (Address (L2.F), Address (L2.F), L2.L, M2_Old, +L1.M);
      Prove_Reach_Preserved (Address (L2.F), Address (L2.F), L2.L, M2_Old, +L1.M);
      Prove_Valid_Preserved (Address (L1.F), Address (L1.F), L1.L, M1_Old, +L1.M);
      Prove_Reach_Preserved (Address (L1.F), Address (L1.F), L1.L, M1_Old, +L1.M);

      --  L1.F and L2.F designate disjoint list segments

      pragma Assert
        (for all A in +L1.M =>
           not Reachable (Address (L2.F), Address (L2.F), L2.L, A, +L1.M)
         or not Reachable (Address (L1.F), Address (L1.F), L1.L, A, +L1.M));

      --  L1.F and L2.F cover the whole memory L1.M

      pragma Assert
        (for all A in +L1.M =>
           Reachable (Address (L2.F), Address (L2.F), L2.L, A, +L1.M)
         or Reachable (Address (L1.F), Address (L1.F), L1.L, A, +L1.M));

      M_Old := +L1.M;
      F1_Next := L_Cell (Deref (L1.M, L1.F)).N;
      F2_Next := L_Cell (Deref (L1.M, L2.F)).N;

      --  Link L2.F to F1_Next.
      --  Use Reference to convert L2.F into an ownership pointer so
      --  its designated value can be updated in place.

      declare
         M1_Access : access Memory_Type := L1.M'Access;
         F2_Ptr    : access Object'Class := Reference (M1_Access, L2.F);
      begin
         L_Cell (F2_Ptr.all).N := F1_Next;
      end;
      pragma Assert (Valid_Memory (+L1.M));
      pragma Assert (L_Cell (Get (+L1.M, Address (L2.F))).N = F1_Next);

      --  The list segments starting at F1_Next and F2_Next are preserved

      if L2.L > 1 then
         Prove_Valid_Preserved (Address (L2.F), Address (F2_Next), L2.L - 1, M_Old, +L1.M);
         Prove_Reach_Preserved (Address (L2.F), Address (F2_Next), L2.L - 1, M_Old, +L1.M);
      end if;
      if L1.L > 1 then
         Prove_Valid_Preserved (Address (L1.F), Address (F1_Next), L1.L - 1, M_Old, +L1.M);
         Prove_Reach_Preserved (Address (L1.F), Address (F1_Next), L1.L - 1, M_Old, +L1.M);
      end if;

      --  They are concatenated to each other

      if L2.L > 1 then
         Prove_Valid_Concat (Address (L2.F), Address (F2_Next), L2.L - 1, Address (L1.F), Address (F1_Next), L1.L - 1, +L1.M);
         Prove_Reach_Concat (Address (L2.F), Address (F2_Next), L2.L - 1, Address (L1.F), Address (F1_Next), L1.L - 1, +L1.M);
      end if;

      --  The list segment starting at F2_Next covers the whole memory L1.M but L1.F

      pragma Assert
        (for all A in +L1.M =>
           Reachable (Address (L1.F), Address (F2_Next), L1.L + L2.L - 1, A, +L1.M)
         or A = Address (L1.F));

      M_Old := +L1.M;

      --  Link L1.F to F2_Next.
      --  Use Reference to convert L1.F into an ownership pointer so
      --  its designated value can be updated in place.

      declare
         M1_Access : access Memory_Type := L1.M'Access;
         F1_Ptr    : access Object'Class := Reference (M1_Access, L1.F);
      begin
         L_Cell (F1_Ptr.all).N := F2_Next;
      end;
      pragma Assert (Valid_Memory (+L1.M));
      pragma Assert (L_Cell (Get (+L1.M, Address (L1.F))).N = F2_Next);

      Prove_Valid_Preserved (Address (L1.F), Address (F2_Next), L1.L + L2.L - 1, M_Old, +L1.M);
      Prove_Reach_Preserved (Address (L1.F), Address (F2_Next), L1.L + L2.L - 1, M_Old, +L1.M);

      pragma Assert (Valid_List (Address (L1.F), Address (L1.F), L1.L + L2.L, +L1.M));

      L1.L := L1.L + L2.L;
   end Merge;

   procedure Do_Test (L1, L2 : in out List) is
      X : List := Create (1); --@RESOURCE_LEAK:FAIL
      Y : List := Create (1);
      --  No attempt is made to deallocate X, we have a memory leak. The cells of
      --  Y are moved to X, so they are not reported as leaked here.
   begin
      Add (X, 2);
      Add (X, 3);
      Add (Y, 2);
      Add (Y, 3);
      pragma Assert (X.L = 3);
      pragma Assert (Y.L = 3);
      Merge (X, Y);
      pragma Assert (X.L = 6);
   end;
begin
   null;
end Example_Recursive;
