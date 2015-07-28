package body Foo
with SPARK_Mode
is

   pragma Warnings (Off, "analyzing unreferenced procedure *");

   G_V  : Natural          := 123;
   G_VC : constant Natural := G_V;
   G_SC : constant Natural := 500;

   procedure Test_01 (A, B : Natural;
                      O    : out Boolean)
   with Global  => null,
        Depends => (O    => B,
                    null => A)
   is
      --  ok
      type T is range 0 .. 100 with Predicate => (A <= Natural (T));

      X : T := T (B);
   begin
      O := X > 10;
   end Test_01;

   procedure Test_02 (A : Natural;
                      B : out Natural;
                      O : out Boolean)
     with Global  => null,
     Depends => (O => A,
                 B => null)
   is
      --  b is uninitialized
      --  b is also not a constant
      type T is range 0 .. 100 with Predicate => (B <= Natural (T));

      X : T := T (A);
   begin
      B := 5;
      O := X > 10;
   end Test_02;

   procedure Test_03 (A, B : Natural;
                      O    : out Boolean)
   with Global  => null,
        Depends => (O => (A, B))
   is
      --  ok
      type T is range 0 .. 100 with Predicate => (A <= Natural (T));

      X : T := T (B);
   begin
      O := X in T;
   end Test_03;

   procedure Test_04 (A, B : Natural;
                      O    : out Boolean)
   with Global  => null,
        Depends => (O => (A, B))
   is
      --  ok
      subtype T is Natural range 0 .. A  with Predicate => (3 <= T);
      subtype U is Natural range 0 .. 10 with Predicate => (B <= U);

      X : Natural := 10;
   begin
      O := X in T | U;
   end Test_04;

   --  Make sure generated globals deal with the predicates fine.
   procedure Test_05 (A, B : Natural;
                      O    : out Boolean)
   with Pre => True  --  WORKAROUND, SEE O728-008
   is
      --  ok
      subtype T is Natural range 0 .. A  with Predicate => (3 <= T);
      subtype U is Natural range 0 .. 10 with Predicate => (B <= U);
      subtype V is Natural range 0 .. 10 with Predicate => (V in G_VC .. G_SC);

      X : Natural := 10;
   begin
      O := X in T | U | V;
   end Test_05;

end Foo;
