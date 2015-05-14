package body Info_Flow_Tests
is

   procedure Test_01 (A : in out Natural;
                      B : in out Natural)
   with Global  => null,
        Depends => (A => B,
                    B => A)
   is
      C1 : constant Natural := A;
      C2 : constant Natural := B;
      type T1 is new Integer range 0 .. C1;
      type T2 is new Integer range 0 .. C2;
   begin
      A := Natural (T2'Last);
      B := Natural (T1'Last);
   end Test_01;

   --  Incorrect
   procedure Test_02 (A : in out Natural;
                      B : in out Natural)
     with Global  => null,
     Depends => (A => B,
                 B => A)
   is
      C1 : constant Natural := A;
      C2 : constant Natural := B;
      type T1 is new Integer range 0 .. C1;
      type T2 is new Integer range 0 .. C2;

      procedure Nested
        with Global => (Output => (A, B))
      is
      begin
         A := Natural (T2'Last);
         B := Natural (T1'Last);
      end Nested;
   begin
      Nested;
   end Test_02;

   procedure Test_03 (A : in out Natural;
                      B : in out Natural)
   with Global  => null,
        Depends => (A => B,
                    B => A)
   is
      C1 : constant Natural := A;
      C2 : constant Natural := B;
      type T1 is new Integer range 0 .. C1;
      type T2 is new Integer range 0 .. C2;

      procedure Nested
      with Global => (Input => (C1, C2),
                      Output => (A, B)),
           Depends => (A => C2,
                       B => C1)
      is
      begin
         A := Natural (T2'Last);
         B := Natural (T1'Last);
      end Nested;
   begin
      Nested;
   end Test_03;

   --  Incorrect
   procedure Test_04 (A : in out Natural)
     with Global => null
   is
      function F1 (X : Natural) return Natural is (X);
      function F2 (X : Natural) return Natural is (A + X);
      function F3 (X : Natural) return Natural is (X)
        with Global => (Proof_In => A), Pre => A >= 0;

      C1 : constant Natural := 5;        -- no vi
      C2 : constant Natural := F1 (5);   -- no vi
      C3 : constant Natural := F2 (5);   -- vi
      C4 : constant Natural := F3 (5);   -- no vi
      C5 : constant Natural := A;        -- vi

      procedure Nested (X : out Natural)
        with Global => (C1, C2, C3, C4, C5)
      is
      begin
         X := C1 + C2 + C3 + C4 + C5;
      end Nested;
      begin
         Nested (A);
      end Test_04;

   procedure Test_05 (A : in out Natural)
   with Global => null
   is
      function F1 (X : Natural) return Natural is (X);
      function F2 (X : Natural) return Natural is (A + X);
      function F3 (X : Natural) return Natural is (X)
        with Global => (Proof_In => A), Pre => A >= 0;

      C1 : constant Natural := 5;        -- no vi
      C2 : constant Natural := F1 (5);   -- no vi
      C3 : constant Natural := F2 (5);   -- vi
      C4 : constant Natural := F3 (5);   -- no vi
      C5 : constant Natural := A;        -- vi

      procedure Nested (X : out Natural)
      with Global => (C3, C5)
      is
      begin
         X := C1 + C2 + C3 + C4 + C5;
      end Nested;
   begin
      Nested (A);
   end Test_05;

   procedure Test_06 (A : in     Natural;
                      B : in out Natural;
                      C :    out Natural)
   is
      C1 : constant Natural := A;
      C2 : constant Natural := B;

      procedure Nested (X : out Natural)
      with Global => C1
      is
         subtype T is Natural range 0 .. C2;
         V : T := C1;
      begin
         X := V;
      end Nested;
   begin
      Nested (B);
      C := C2;
   end Test_06;

   procedure Test_07 (A : in     Natural;
                      B : in out Natural;
                      C :    out Natural)
   is
      C1 : constant Natural := A;
      C2 : constant Natural := B;

      procedure Nested (X : out Natural)
      with Global => C1
      is
         subtype T is Natural range 0 .. C2;
      begin
         X := 0;
         for I in T loop -- !!! Missing dependency here
            X := I;
         end loop;
      end Nested;
   begin
      Nested (B);
      C := C2;
   end Test_07;

end Info_Flow_Tests;
