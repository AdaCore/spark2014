with Interfaces; use Interfaces;
with Ada.Numerics.Big_Numbers.Big_Integers; use Ada.Numerics.Big_Numbers.Big_Integers;
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
     Pre => Valid_Memory (M) and then Valid_List (F, A1, L, M);
   --  A is reachable in a cyclic list

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

   function Create (V : Natural) return List with
     Post => Valid_List (Create'Result)
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

   procedure Add (L : in out List; V : Natural) with
     Pre  => Valid_List (L) and then L.L < Natural'Last,
     Post => Valid_List (L) and then L.L = L.L'Old + 1;

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
      end if;

      L.L := L.L + 1;
   end Add;

   X : List := Create (1); --@RESOURCE_LEAK:FAIL
   Y : List := Create (1); --@RESOURCE_LEAK:FAIL
   --  No attempt is made to deallocate X and Y, we have a memory leak
begin
   Add (X, 2);
   Add (X, 3);
   Add (Y, 2);
   Add (Y, 3);
   pragma Assert (X.L = 3);
   pragma Assert (Y.L = 3);
end Example_Recursive;
