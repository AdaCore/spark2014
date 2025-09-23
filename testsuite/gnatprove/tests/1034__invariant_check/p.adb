procedure P with SPARK_Mode is
   package G is
      type R is private;
      type A is private;
      type I is private;

      function "=" (X, Y : R) return Boolean;
      function "=" (X, Y : A) return Boolean;
   private
      type R is record
         N, D : Natural := 1;
      end record with
        Type_Invariant => D /= 0;

      function "=" (X, Y : R) return Boolean is (X.N / X.D = Y.N / Y.D);

      type A is array (Positive range 1 .. 2) of Natural with
        Default_Component_Value => 1,
        Type_Invariant => A (2) /= 0;

      function "=" (X, Y : A) return Boolean is (X (1) / X (2) = Y (1) / Y (2));

      type I is new Integer with
        Default_Value => 1,
        Type_Invariant => I /= 0;

   end G;

   package body G is

      type R_Holder_R is record
         F : I;
	 G : Integer;
         C : R;
         D : R;
      end record;

      procedure Test_R_Holder_R (A, B : R_Holder_R) with Global => null is
         R : Boolean;
      begin
         R := A = B;  -- @INVARIANT_CHECK:FAIL
      end Test_R_Holder_R;

      procedure Test_R_Holder_R_2 (A, B : R_Holder_R) with
        Global => null,
        Pre => A.C.D /= 0 and B.C.D /= 0
      is
         R : Boolean;
      begin
         R := A = B;  -- @INVARIANT_CHECK:FAIL
      end Test_R_Holder_R_2;

      procedure Test_R_Holder_R_3 (A, B : R_Holder_R) with
        Global => null,
        Pre => A.D.D /= 0 and B.D.D /= 0
      is
         R : Boolean;
      begin
         R := A = B;  -- @INVARIANT_CHECK:FAIL
      end Test_R_Holder_R_3;

      procedure Test_R_Holder_R_4 (A, B : R_Holder_R) with
        Global => null,
        Pre => A.C.D /= 0 and B.C.D /= 0 and A.D.D /= 0 and B.D.D /= 0
       is
         R : Boolean;
      begin
         R := A = B;  -- @INVARIANT_CHECK:PASS
      end Test_R_Holder_R_4;

      type R_Holder_A is array (Positive range <>) of R;

      procedure Test_R_Holder_A (A, B : R_Holder_A) with Global => null;

      procedure Test_R_Holder_A (A, B : R_Holder_A) is
         R : Boolean;
      begin
         R := A = B;  -- @INVARIANT_CHECK:FAIL
      end Test_R_Holder_A;

      procedure Test_R_Holder_A_2 (A, B : R_Holder_A) with
        Global => null,
        Pre => 1 in A'Range and then 1 in B'Range and then A (1).D /= 0 and then B (1).D /= 0
      is
         R : Boolean;
      begin
         R := A = B;  -- @INVARIANT_CHECK:FAIL
      end Test_R_Holder_A_2;

      procedure Test_R_Holder_A_3 (A, B : R_Holder_A) with
        Global => null,
        Pre => A'Length = 0 and B'Length = 0
      is
         R : Boolean;
      begin
         R := A = B;  -- @INVARIANT_CHECK:PASS
      end Test_R_Holder_A_3;

      type R_Holder_DR (P : Boolean; L : Natural) is record
         D : R_Holder_A (1 .. L);
         case P is
         when True =>
            C : R;
         when False => null;
         end case;
      end record;

      procedure Test_R_Holder_DR (A, B : R_Holder_DR) with Global => null is
         R : Boolean;
      begin
         R := A = B;  -- @INVARIANT_CHECK:FAIL
      end Test_R_Holder_DR;

      procedure Test_R_Holder_DR_2 (A, B : R_Holder_DR) with
        Global => null,
        Pre => not A.P and not B.P
      is
         R : Boolean;
      begin
         R := A = B;  -- @INVARIANT_CHECK:FAIL
      end Test_R_Holder_DR_2;

      procedure Test_R_Holder_DR_3 (A, B : R_Holder_DR) with
        Global => null,
        Pre => A.L = 0 and B.L = 0
      is
         R : Boolean;
      begin
         R := A = B;  -- @INVARIANT_CHECK:FAIL
      end Test_R_Holder_DR_3;

      procedure Test_R_Holder_DR_4 (A, B : R_Holder_DR) with
        Global => null,
        Pre => not A.P and not B.P and A.L = 0 and B.L = 0
      is
         R : Boolean;
      begin
         R := A = B;  -- @INVARIANT_CHECK:PASS
      end Test_R_Holder_DR_4;

      type A_Holder_R is record
         C : A;
      end record;

      procedure Test_A_Holder_R (A, B : A_Holder_R) with Global => null is
         R : Boolean;
      begin
         R := A = B;  -- @INVARIANT_CHECK:NONE
      end Test_A_Holder_R;

      type A_Holder_A is array (Positive range <>) of A;

      procedure Test_A_Holder_A (A, B : A_Holder_A) with Global => null is
         R : Boolean;
      begin
         R := A = B;  -- @INVARIANT_CHECK:NONE
      end Test_A_Holder_A;

      procedure Test_Mem (A, B, C : R_Holder_R) with
        Global => null,
        Pre => B.C.D /= 0 and B.D.D /= 0 and C.C.D /= 0 and C.D.D /= 0
      is
         R : Boolean;
      begin
         R := A in B | C;  -- @INVARIANT_CHECK:FAIL
      end Test_Mem;

      procedure Test_Mem_2 (A, B, C : R_Holder_R) with
        Global => null,
        Pre => A.C.D /= 0 and A.D.D /= 0
      is
         R : Boolean;
      begin
         R := A in B | C;  -- @INVARIANT_CHECK:FAIL
      end Test_Mem_2;

      procedure Test_Mem_3 (A, B, C : R_Holder_R) with
        Global => null,
        Pre => A.C.D /= 0 and A.D.D /= 0 and B.C.D /= 0 and B.D.D /= 0
      is
         R : Boolean;
      begin
         R := A in B | C;  -- @INVARIANT_CHECK:FAIL
      end Test_Mem_3;

      procedure Test_Mem_4 (A, B, C : R_Holder_R) with
        Global => null,
        Pre => A.C.D /= 0 and A.D.D /= 0 and B.C.D /= 0 and B.D.D /= 0 and C.C.D /= 0 and C.D.D /= 0
      is
         R : Boolean;
      begin
         R := A in B | C;  -- @INVARIANT_CHECK:PASS
      end Test_Mem_4;

      procedure Test_Mem_5 (A, B : R_Holder_R) with
        Global => null,
        Pre => A.C.D /= 0 and A.D.D /= 0
      is
         R : Boolean;
      begin
         R := A in B;  -- @INVARIANT_CHECK:FAIL
      end Test_Mem_5;

      procedure Test_Mem_6 (A, B : R_Holder_R) with
        Global => null,
        Pre => B.C.D /= 0 and B.D.D /= 0
      is
         R : Boolean;
      begin
         R := A in B;  -- @INVARIANT_CHECK:FAIL
      end Test_Mem_6;

      procedure Test_Mem_7 (A, B : R_Holder_R) with
        Global => null,
        Pre => A.C.D /= 0 and A.D.D /= 0 and B.C.D /= 0 and B.D.D /= 0
      is
         R : Boolean;
      begin
         R := A in B;  -- @INVARIANT_CHECK:PASS
      end Test_Mem_7;

      procedure Test_Mem_8 (A, B, C : R) with
        Global => null
      is
         R : Boolean;
      begin
         R := A in B | C;  -- @INVARIANT_CHECK:FAIL
      end Test_Mem_8;

   end G;

begin
   null;
end;
