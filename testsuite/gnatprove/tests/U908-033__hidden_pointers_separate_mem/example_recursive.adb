pragma Ada_2022;

with Interfaces;              use Interfaces;
with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with SPARK.Pointers.Explicit_Reclamation.Separate_Memory;
with SPARK.Pointers.Handles.Plain_Handles; use SPARK.Pointers.Handles;
with SPARK.Containers.Functional.Sets;
with SPARK.Containers.Functional.Infinite_Sequences;
with SPARK.Pointers.Abstract_Reachability;

procedure Example_Recursive with SPARK_Mode is
   pragma Unevaluated_Use_Of_Old (Allow);

   --  Use an abstract handle to hold the pointer type in the recursive
   --  definition. As we use pointers with aliasing in a separate memory model,
   --  the pointer type is not subject to ownership and we can use simple
   --  handles here.

   type L_Cell is record
      V : Natural;
      N : Plain_Handles.Handle;
   end record;

   package List_Pointers is new
     SPARK.Pointers.Explicit_Reclamation.Separate_Memory (L_Cell);

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
      M : aliased Memory_Type;
      F : Pointer;
      L : Positive;
   end record;

   --  This test reimplements reachability instead of using Abstract_Reachability
   --  which only works on acyclic lists.

   function Valid_List (F, A : Pointer; L : Positive; M : Memory_Map) return Boolean is
     (F /= Null_Pointer and then A /= Null_Pointer and then In_Memory (M, F) and then In_Memory (M, A) and then
        (if L = 1 then Of_Handle (Get (M, A).N) = F
         else Of_Handle (Get (M, A).N) /= F
         and then Valid_List (F, Of_Handle (Get (M, A).N), L - 1, M)))
   with Subprogram_Variant => (Decreases => L),
     Global => null,
     Pre => Valid_Memory (M),
     Ghost => Static;

   function Valid_List (L : List) return Boolean is
     (Valid_Memory (+L.M)
      and then Valid_List (L.F, L.F, L.L, +L.M))
   with Ghost => Static;
   -- L is a cyclic list

   function Reachable (F, A1 : Pointer; L : Positive; A2 : Pointer; M : Memory_Map) return Boolean is
     (A1 = A2
      or else (L > 1 and then Reachable (F, Of_Handle (Get (M, A1).N), L - 1, A2, M)))
   with Subprogram_Variant => (Decreases => L),
     Global => null,
     Ghost => Static,
     Pre  => Valid_Memory (M) and then Valid_List (F, A1, L, M),
     Post => (if Reachable'Result then In_Memory (M, A2));
   --  A is reachable in a cyclic list

   function Valid_List_No_Leak (L : List) return Boolean is
     (Valid_List (L)
      and then (for all A in +L.M =>
                     Reachable (L.F, L.F, L.L, A, +L.M)))
   with Ghost => Static;
   --  All cells of L.M are reachable from L.F

   --  Lemma:
   --    Valid lists are preserved if the reachable elements are not modified
   procedure Prove_Valid_Preserved (F, A : Pointer; L : Positive; M1, M2 : Memory_Map) with
     Subprogram_Variant => (Decreases => L),
     Ghost => Static,
     Global => null,
     Pre => Valid_Memory (M1) and then Valid_Memory (M2) and then Valid_List (F, A, L, M1)
     and then In_Memory (M2, F)
     and then (for all A2 in M1 =>
                 (if Reachable (F, A, L, A2, M1) and then (F = A or A2 /= F)
                  then In_Memory (M2, A2) and then Eq (Get (M1, A2).all, Get (M2, A2).all))),
     Post => Valid_List (F, A, L, M2)
   is
   begin
      if L = 1 then
         return;
      elsif F /= A and L = 2 then
         return;
      else
         Prove_Valid_Preserved (F, Of_Handle (Get (M1, A).N), L - 1, M1, M2);
         pragma Assert (Valid_List (F, A, L, M2));
      end if;
   end Prove_Valid_Preserved;

   --  Lemma:
   --    Reachability is preserved if the reachable elements are not modified
   procedure Prove_Reach_Preserved (F, A : Pointer; L : Positive; M1, M2 : Memory_Map) with
     Subprogram_Variant => (Decreases => L),
     Ghost => Static,
     Global => null,
     Pre => Valid_Memory (M1) and then Valid_Memory (M2) and then Valid_List (F, A, L, M1)
     and then In_Memory (M2, F)
     and then (for all A2 in M1 =>
                 (if Reachable (F, A, L, A2, M1) and then (F = A or A2 /= F)
                  then In_Memory (M2, A2) and then Eq (Get (M1, A2).all, Get (M2, A2).all))),
     Post => (for all A2 in M2 => Reachable (F, A, L, A2, M1) = Reachable (F, A, L, A2, M2))
   is
   begin
      if L = 1 then
         return;
      elsif L > 2 then
         Prove_Reach_Preserved (F, Of_Handle (Get (M1, A).N), L - 1, M1, M2);
      end if;
      Prove_Valid_Preserved (F, A, L, M1, M2);
   end Prove_Reach_Preserved;

   --  Lemma:
   --    Concatenating two valid list segments creates a valid list segment
   procedure Prove_Valid_Concat
     (F1, A1 : Pointer; L1 : Positive;
      F2, A2 : Pointer; L2 : Natural; M : Memory_Map)
   with
     Subprogram_Variant => (Decreases => L1),
     Ghost => Static,
     Global => null,
     Pre => Valid_Memory (M)
       and then L1 < Positive'Last - L2
       and then Valid_List (F1, A1, L1, M)
       and then (if L2 = 0 then F2 = A2 and then In_Memory (M, F2)
                 else F2 /= A2 and then Valid_List (F2, A2, L2, M))
       and then not Reachable (F1, A1, L1, F2, M)
       and then F1 /= F2
       and then Of_Handle (Get (M, F1).N) = A2,
     Post => Valid_List (F2, A1, L1 + L2 + 1, M)
   is
   begin
      if L1 = 1 then
         return;
      else
         Prove_Valid_Concat (F1, Of_Handle (Get (M, A1).N), L1 - 1, F2, A2, L2, M);
      end if;
   end Prove_Valid_Concat;

   --  Lemma:
   --    The elements reachable in the concatenation of two valid list segments
   --    are the elements reachable in each segments plus the middle one.
   procedure Prove_Reach_Concat
     (F1, A1 : Pointer; L1 : Positive;
      F2, A2 : Pointer; L2 : Natural; M : Memory_Map)
   with
     Subprogram_Variant => (Decreases => L1),
     Ghost => Static,
     Global => null,
     Pre => Valid_Memory (M)
       and then L1 < Positive'Last - L2
       and then Valid_List (F1, A1, L1, M)
       and then (if L2 = 0 then F2 = A2 and then In_Memory (M, F2)
                 else F2 /= A2 and then Valid_List (F2, A2, L2, M))
       and then not Reachable (F1, A1, L1, F2, M)
       and then F1 /= F2
       and then Of_Handle (Get (M, F1).N) = A2,
     Post => (for all B in M => Reachable (F2, A1, L1 + L2 + 1, B, M) =
                (Reachable (F1, A1, L1, B, M) or B = F1
                 or (L2 > 0 and then Reachable (F2, A2, L2, B, M))))
   is
   begin
      if L1 = 1 then
         return;
      else
         Prove_Reach_Concat (F1, Of_Handle (Get (M, A1).N), L1 - 1, F2, A2, L2, M);
         Prove_Valid_Concat (F1, Of_Handle (Get (M, A1).N), L1 - 1, F2, A2, L2, M);
      end if;
   end Prove_Reach_Concat;

   function Get (F, A : Pointer; P, L : Positive; M : Memory_Map) return Natural is
     (if P = 1 then Get (M, A).V
      else Get (F, Of_Handle (Get (M, A).N), P - 1, L - 1, M))
   with Subprogram_Variant => (Decreases => L),
     Global => null,
     Pre => (Static => Valid_Memory (M) and then In_Memory (M, F)
     and then Valid_List (F, A, L, M) and then P <= L),
     Ghost;

   function Get (L : List; P : Positive) return Natural is
     (Get (L.F, L.F, P, L.L, +L.M))
   with
     Global => null,
     Pre => (Static => Valid_List (L) and then P <= L.L),
     Ghost;

   --  Create a cyclic list containing a single cell
   function Create (V : Natural) return List with
     Volatile_Function,
     Post => (Static => Valid_List_No_Leak (Create'Result)
     and then Create'Result.L = 1
     and then Get (Create'Result, 1) = V);

   function Create (V : Natural) return List is
      M : aliased Memory_Type := Empty_Map;
      F : Pointer;
   begin
      Create_Copy (M, L_Cell'(V, To_Handle (Null_Pointer)), F);
      pragma Assert (Get (+M, F).V = V);

      --  Use Reference to convert F into an ownership pointer so
      --  its designated value can be updated in place.

      declare
         F_Ptr : access L_Cell := Reference (M, F);
      begin
         F_Ptr.N := To_Handle (F);
      end;

      pragma Assert (Static => Valid_Memory (+M));
      pragma Assert (Static => Of_Handle (Get (+M, F).N) = F);

      return (M => M, F => F, L => 1);
   end Create;

   --  Insert a value in a cyclic list
   procedure Add (L : in out List; V : Natural) with
     Pre  => (Static => Valid_List_No_Leak (L) and then L.L < Natural'Last),
     Post => (Static => Valid_List_No_Leak (L) and then L.L = L.L'Old + 1);

   procedure Add (L : in out List; V : Natural) is
      F_Next : Plain_Handles.Handle := Deref (L.M, L.F).N;
      New_P  : Pointer;
      M_Old  : constant Memory_Map := +L.M with Ghost;
   begin
      Create_Copy (L.M, L_Cell'(V, F_Next), New_P);
      pragma Assert (Static => Valid_Memory (+L.M));

      --  Use Reference to convert L.F into an ownership pointer so
      --  its designated value can be updated in place.

      declare
         F_Ptr : access L_Cell := Reference (L.M, L.F);
      begin
         F_Ptr.N := To_Handle (New_P);
      end;

      pragma Assert (Static => Valid_Memory (+L.M));
      pragma Assert (Static => Of_Handle (Get (+L.M, L.F).N) = New_P);
      pragma Assert (Static => Get (+L.M, New_P).N = F_Next);

      if L.L > 1 then
         Prove_Valid_Preserved (L.F, Of_Handle (F_Next), L.L - 1, M_Old, +L.M);
         Prove_Reach_Preserved (L.F, Of_Handle (F_Next), L.L - 1, M_Old, +L.M);
      end if;

      L.L := L.L + 1;
   end Add;

   --  Merge 2 cyclic lists
   procedure Merge (L1, L2 : in out List) with
     Pre  => (Static => Valid_List_No_Leak (L1) and then Valid_List_No_Leak (L2)
     and then L1.L <= Natural'Last - L2.L),
     Post => (Static => Valid_List_No_Leak (L1) and then Is_Empty (L2.M)
     and then L1.L = L1.L'Old + L2.L'Old);

   procedure Merge (L1, L2 : in out List) is

      function Valid_In (P : Pointer; F : Pointer; L : Positive) return Boolean is
        (P = F or else (L > 1 and then Valid_In (P, Of_Handle (Constant_Reference (L2.M, F).N), L - 1)))
        with Pre => (Static => Valid_Memory (+L2.M) and then Valid_List (L2.F, F, L, +L2.M)),
        Post => Valid_In'Result =
          Reachable (L2.F, F, L, P, +L2.M),
          Subprogram_Variant => (Decreases => L);

      function Valid_In_L2 (P : Pointer) return Boolean with
        Pre  => (Static => Valid_List_No_Leak (L2)),
        Post =>
          (Static => Valid_In_L2'Result = In_Memory (+L2.M, P));

      function Valid_In_L2 (P : Pointer) return Boolean is
      begin
         return Valid_In (P, L2.F, L2.L);
      end Valid_In_L2;

      F1_Next : Plain_Handles.Handle;
      F2_Next : Plain_Handles.Handle;
      M1_Old  : constant Memory_Map := +L1.M with Ghost;
      M2_Old  : constant Memory_Map := +L2.M with Ghost;
      M_Old   : Memory_Map with Ghost;
   begin
      Move_Memory (L2.M, L1.M, Elements (Valid_In_L2'Access));
      pragma Assert (Static => Valid_Memory (+L1.M));

      Prove_Valid_Preserved (L2.F, L2.F, L2.L, M2_Old, +L1.M);
      Prove_Reach_Preserved (L2.F, L2.F, L2.L, M2_Old, +L1.M);
      Prove_Valid_Preserved (L1.F, L1.F, L1.L, M1_Old, +L1.M);
      Prove_Reach_Preserved (L1.F, L1.F, L1.L, M1_Old, +L1.M);

      --  L1.F and L2.F designate disjoint list segments

      pragma Assert
        (Static => (for all A in +L1.M =>
           not Reachable (L2.F, L2.F, L2.L, A, +L1.M)
         or not Reachable (L1.F, L1.F, L1.L, A, +L1.M)));

      --  L1.F and L2.F cover the whole memory L1.M

      pragma Assert
        (Static => (for all A in +L1.M =>
           Reachable (L2.F, L2.F, L2.L, A, +L1.M)
         or Reachable (L1.F, L1.F, L1.L, A, +L1.M)));

      M_Old := +L1.M;
      F1_Next := L_Cell (Deref (L1.M, L1.F)).N;
      F2_Next := L_Cell (Deref (L1.M, L2.F)).N;

      --  Link L2.F to F1_Next.
      --  Use Reference to convert L2.F into an ownership pointer so
      --  its designated value can be updated in place.

      declare
         F2_Ptr : access L_Cell := Reference (L1.M, L2.F);
      begin
         F2_Ptr.N := F1_Next;
      end;
      pragma Assert (Static => Valid_Memory (+L1.M));
      pragma Assert (Static => Get (+L1.M, L2.F).N = F1_Next);

      --  Prove that the list segment starting at F2_Next covers the whole memory L1.M but L1.F

      begin
         --  The list segments starting at F1_Next and F2_Next are preserved

         if L2.L > 1 then
            Prove_Valid_Preserved (L2.F, Of_Handle (F2_Next), L2.L - 1, M_Old, +L1.M);
            Prove_Reach_Preserved (L2.F, Of_Handle (F2_Next), L2.L - 1, M_Old, +L1.M);
         end if;
         if L1.L > 1 then
            Prove_Valid_Preserved (L1.F, Of_Handle (F1_Next), L1.L - 1, M_Old, +L1.M);
            Prove_Reach_Preserved (L1.F, Of_Handle (F1_Next), L1.L - 1, M_Old, +L1.M);
         end if;

         --  They are concatenated to each other

         if L2.L > 1 then
            Prove_Valid_Concat (L2.F, Of_Handle (F2_Next), L2.L - 1, L1.F, Of_Handle (F1_Next), L1.L - 1, +L1.M);
            Prove_Reach_Concat (L2.F, Of_Handle (F2_Next), L2.L - 1, L1.F, Of_Handle (F1_Next), L1.L - 1, +L1.M);

            pragma Assert
              (Static => (for all A in +L1.M =>
                 Reachable (L1.F, Of_Handle (F2_Next), L1.L + L2.L - 1, A, +L1.M)
               or A = L1.F));
         end if;

         pragma Assert_And_Cut
           (Static => (Valid_List (L1.F, Of_Handle (F2_Next), L1.L + L2.L - 1, +L1.M)
            and
              (for all A in +L1.M =>
                   Reachable (L1.F, Of_Handle (F2_Next), L1.L + L2.L - 1, A, +L1.M)
               or A = L1.F)));
      end;

      M_Old := +L1.M;

      --  Link L1.F to F2_Next.
      --  Use Reference to convert L1.F into an ownership pointer so
      --  its designated value can be updated in place.

      declare
         F1_Ptr : access L_Cell := Reference (L1.M, L1.F);
      begin
         F1_Ptr.N := F2_Next;
      end;
      pragma Assert (Static => Valid_Memory (+L1.M));
      pragma Assert (Static => Get (+L1.M, L1.F).N = F2_Next);

      Prove_Valid_Preserved (L1.F, Of_Handle (F2_Next), L1.L + L2.L - 1, M_Old, +L1.M);
      Prove_Reach_Preserved (L1.F, Of_Handle (F2_Next), L1.L + L2.L - 1, M_Old, +L1.M);

      pragma Assert (Static => Valid_List (L1.F, L1.F, L1.L + L2.L, +L1.M));

      L1.L := L1.L + L2.L;
   end Merge;

   procedure Do_Test is
      X : List := Create (1); --@RESOURCE_LEAK_AT_END_OF_SCOPE:FAIL
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
   Do_Test;
end Example_Recursive;
