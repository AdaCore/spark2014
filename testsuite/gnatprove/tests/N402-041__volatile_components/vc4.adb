package body VC4
  with SPARK_Mode => On
is

   procedure F0 (X : in A0; R : out Boolean)
   is
      T1, T2, T3, T4 : Integer;
   begin
      -- A0 and V0 are NOT volatile, so successive reads
      -- should be known to be equal
      T1 := X (2);
      T2 := X (2);
      pragma Assert (T1 = T2); --@ASSERT:PASS

      T3 := V0 (2);
      T4 := V0 (2);
      pragma Assert (T3 = T4); --@ASSERT:PASS

      R := (T1 = T2) and (T3 = T4);
   end F0;

   procedure F1 (X : in A1; R : out Boolean)
   is
      T1, T2, T3, T4 : Integer;
   begin
      -- A1 and V1 are Volatile, so successive reads
      -- MIGHT NOT be equal
      T1 := X (2);
      T2 := X (2);
      pragma Assert (T1 = T2); --@ASSERT:FAIL

      T3 := V1 (2);
      T4 := V1 (2);
      pragma Assert (T3 = T4); --@ASSERT:FAIL

      R := (T1 = T2) and (T3 = T4);
   end F1;

   procedure F2 (X : in A2; R : out Boolean)
   is
      T1, T2, T3, T4 : Integer;
   begin
      -- A2 and V2 have Volatile_Components, so successive reads
      -- MIGHT NOT be equal
      T1 := X (2);
      T2 := X (2);
      pragma Assert (T1 = T2); --@ASSERT:FAIL

      T3 := V2 (2);
      T4 := V2 (2);
      pragma Assert (T3 = T4); --@ASSERT:FAIL

      R := (T1 = T2) and (T3 = T4);
   end F2;

   procedure F3 (X : in A3; R : out Boolean)
   is
      T1, T2, T3, T4 : Integer;
   begin
      -- A3 and V3 are Volatile and have Volatile_Components, so successive
      -- reads MIGHT NOT be equal

      T1 := X (2);
      T2 := X (2);
      pragma Assert (T1 = T2); --@ASSERT:FAIL

      T3 := V3 (2);
      T4 := V3 (2);
      pragma Assert (T3 = T4); --@ASSERT:FAIL

      R := (T1 = T2) and (T3 = T4);
   end F3;

   procedure F4 (R : out Boolean)
   is
      T1, T2 : Integer;
   begin
      T1 := V4 (2);
      T2 := V4 (2);
      pragma Assert (T1 = T2); --@ASSERT:FAIL

      R := (T1 = T2);
   end F4;


end VC4;
