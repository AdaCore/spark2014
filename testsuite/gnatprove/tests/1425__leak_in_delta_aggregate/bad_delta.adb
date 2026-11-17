with Ada.Unchecked_Deallocation;
procedure Bad_Delta with SPARK_Mode is
   type IAcc is access Integer;
   type A is array (Integer range <>) of IAcc;
   type M is array (Integer range 1 .. 42, Integer range 1 .. 42) of IAcc;
   U : A := ((1 .. 42 => new Integer'(0)) with delta 36 => new Integer'(1)); --@RESOURCE_LEAK:FAIL
   -- Location designed by cell 36 is leaked.

   type R is record
      X : A (1 .. 10);
      Y : IAcc;
      Z : Integer;
   end record;

   type Pair is record
      F : R;
      L : R;
   end record;

   function Make return R is (X => (1 .. 10 => new Integer'(1)),
                              Y => new Integer'(2),
                              Z => 3);

   V : R := Make;
   W : R := (V with delta Y => new Integer'(2));  --@RESOURCE_LEAK:FAIL
   B : R := (Make with delta Z => 2); --@RESOURCE_LEAK:NONE
   C : R := (Make with delta X (3) => new Integer'(3), Z => 36); --@RESOURCE_LEAK:FAIL
   D : R := (Make with delta Y => new Integer'(4), Z => 42); --@RESOURCE_LEAK:FAIL
   E : Pair := ((F => Make, L => Make) with delta F.Y => new Integer'(42)); --@RESOURCE_LEAK:FAIL
   G : Pair := ((F => Make, L => Make) with delta F.Y => null, --@RESOURCE_LEAK:FAIL
             L => Make); --@RESOURCE_LEAK:FAIL
   H : Pair := (G with delta F.Y => new Integer'(36)); --@RESOURCE_LEAK:PASS

   Low : M := (1 .. 42 => (1 .. 42 => new Integer'(48)));
   Upd : IAcc := new Integer'(54);
   Up : M := Low'Update((2,3) => Upd); --@RESOURCE_LEAK:FAIL
   Gh : R := (Make with delta Y => new Integer'(4), Z => 42) with Ghost => Static; --@RESOURCE_LEAK:NONE
   Gh2 : R := (Make with delta Y => new Integer'(4),Z => 42) with Ghost; --@RESOURCE_LEAK:FAIL

   procedure Free is new Ada.Unchecked_Deallocation (Integer, IAcc);
   procedure Dealloc (A : in out R) with Post =>
     (for all I in 1 .. 10 => A.X (I) = null)
     and then A.Y = null;
   procedure Dealloc (A : in out R) is
   begin
      for I in 1 .. 10 loop
         pragma Loop_Invariant (for all J in 1 .. I - 1 => A.X (J) = null);
         Free (A.X (I));
      end loop;
      Free (A.Y);
   end Dealloc;
   procedure Dealloc_Ghost (A : in out R) with Ghost, Post =>
     (for all I in 1 .. 10 => A.X (I) = null)
     and then A.Y = null;
   procedure Dealloc_Ghost (A : in out R) is
   begin
      Dealloc (A);
   end Dealloc_Ghost;
   procedure In_Ghost_Static with Ghost => Static;
   procedure In_Ghost_Static is
      Gh3 : R := (Make with delta Y => new Integer'(4), Z => 42); --@RESOURCE_LEAK:NONE
   begin
      null;
   end In_Ghost_Static;
   procedure In_Ghost with Ghost;
   procedure In_Ghost is
      Gh4 : R := (Make with delta Y => new Integer'(4), Z => 42); --@RESOURCE_LEAK:FAIL
   begin
      Dealloc (Gh4);
   end In_Ghost;
begin
   for I in 1 .. 42 loop
      pragma Loop_Invariant (for all J in 1 .. I - 1 => U (J) = null);
      pragma Loop_Invariant (for all J in 1 .. I - 1 =>
                               (for all K in 1 .. 42 => Up (J,K) = null));
      Free (U (I));
      for J in 1 .. 42 loop
         pragma Loop_Invariant (for all K in 1 .. I =>
                                  (for all L in 1 .. 42 =>
                                     (if K < I or else L < J
                                      then Up (K,L) = null)));
         Free (Up (I,J));
      end loop;
   end loop;
   Dealloc (W);
   Dealloc (B);
   Dealloc (C);
   Dealloc (D);
   Dealloc (E.F);
   Dealloc (E.L);
   Dealloc (H.F);
   Dealloc (H.L);
   Dealloc_Ghost (Gh2);
   In_Ghost;
   In_Ghost_Static;
end Bad_Delta;
