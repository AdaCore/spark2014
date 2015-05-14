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
      function F4 (X, Y : Natural) return Natural is (X)
        with Depends => (F4'Result => X,
                         null      => Y),
             Pre => Y > 0,
             Post => Y > 0;

      C1 : constant Natural := 5;            -- no vi
      C2 : constant Natural := F1 (5);       -- no vi
      C3 : constant Natural := F2 (5);       -- vi
      C4 : constant Natural := F3 (5);       -- no vi
      C5 : constant Natural := A;            -- vi
      C6 : constant Natural := F4 (C1, C3);  -- no vi
      C7 : constant Natural := F4 (C3, C4);  -- vi

      procedure Nested (X : out Natural)
        with Global => (C1, C2, C3, C4, C5, C6, C7)
      is
      begin
         X := C1 + C2 + C3 + C4 + C5 + C6 + C7;
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
      function F4 (X, Y : Natural) return Natural is (X)
        with Depends => (F4'Result => X,
                         null      => Y),
             Pre => Y > 0,
             Post => Y > 0;

      C1 : constant Natural := 5;            -- no vi
      C2 : constant Natural := F1 (5);       -- no vi
      C3 : constant Natural := F2 (5);       -- vi
      C4 : constant Natural := F3 (5);       -- no vi
      C5 : constant Natural := A;            -- vi
      C6 : constant Natural := F4 (C1, C3);  -- no vi
      C7 : constant Natural := F4 (C3, C4);  -- vi

      procedure Nested (X : out Natural)
      with Global => (C3, C5, C7)
      is
      begin
         X := C1 + C2 + C3 + C4 + C5 + C6 + C7;
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

   --  Incorrect
   procedure Test_07 (A : in     Natural;
                      B : in out Natural;
                      C :    out Natural)
   is
      C1 : constant Natural := A;
      C2 : constant Natural := B;

      procedure Nested (X : out Natural)
      with Global => C1
      is
         subtype T is Natural range C1 .. C2;
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

   procedure Test_08 (A : in     Natural;
                      B : in     Natural;
                      C :    out Boolean)
   with Global  => null,
        Depends => (C => (A, B))
   is
      subtype T is Natural range A .. A;
   begin
      --  !!! Missing dependency in quantifier
      C := (for all I in T => I = B);  --  C := A = B
   end Test_08;

   procedure Test_09 (A : in     Natural;
                      B : in     Natural;
                      C :    out Boolean)
   with Global  => null,
        Depends => (C => (A, B))
   is
      subtype T is Natural range A .. A;
   begin
      --  !!!  Missing dependency here
      --  Another strange way of writing C := A = B
      if B in T then
         C := True;
      else
         C := False;
      end if;
   end Test_09;

   procedure Test_11 (A : in     Natural;
                      B : in     Natural;
                      C :    out Boolean)
   with Global  => null,
        Depends => (C => (A, B))
   is
      subtype T is Natural range A .. A;
   begin
      --  !!!  Missing dependency here
      --  Another strange way of writing C := A = B
      C := (if B in T then True else False);
   end Test_11;

   procedure Test_12 (A : in     Natural;
                      B : in     Natural;
                      C :    out Natural;
                      D :    out Natural;
                      E :    out Natural;
                      F :    out Boolean)
   with Global  => null,
        Depends => ((F, C) => B,
                    D      => A,
                    E      => null)
   is
      subtype T1 is Natural range A .. B;
      type T2 is new T1;
      subtype T3 is T2 range 0 .. T2'Last;
      type T4 is new Natural range Natural (T3'First) .. Natural (T3'Last);
   begin
      C := Natural (T4'Last);
      D := Natural (T2'First);
      E := Natural (T4'First);
      F := 5 in T4;
   end Test_12;


end Info_Flow_Tests;
