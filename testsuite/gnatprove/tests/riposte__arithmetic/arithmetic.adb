package body Arithmetic
is
   type Unsigned_Byte is range 0..255;
   type Byte is range -128..127;

   function Minus_I (A, B: Integer) return Integer
     with Post => Minus_I'Result = A - B
   is
   begin
      return A - B;  --  @OVERFLOW_CHECK:FAIL @COUNTEREXAMPLE
   end Minus_I;

   function Negation_I (A: Integer) return Integer
     with Post => Negation_I'Result = -A
   is
   begin
      return -A;  --  @OVERFLOW_CHECK:FAIL @COUNTEREXAMPLE
   end Negation_I;

   function Multiply_A (A, B: Integer) return Integer
     with Post => Multiply_A'Result = A * B
   is
   begin
      return A * B;  --  @OVERFLOW_CHECK:FAIL
   end Multiply_A;

   function Multiply_B(A, B: Unsigned_Byte) return Integer
   is
      R : Integer;
   begin
      R := 0;
      for I in Unsigned_Byte range 1..B loop
         R := R + Integer(A);
         pragma Loop_Invariant (R = Integer(I) * Integer(A)
                                  and B = B'Loop_Entry);
      end loop;
      return R;
   end Multiply_B;

   function Multiply_C (A, B: in Unsigned_Byte) return Unsigned_Byte
     with Pre => A = 6 and B = 40
   is
      R : Unsigned_Byte;
   begin
      R := A * B;
      return R;
   end Multiply_C;

   --  "Doubles, because they are the biggest types there are."
   --     - Unknown Student
   pragma Warnings (Off, "* has no effect");
   procedure RSA_Small (Double_A, Double_B: in Natural)
     with Depends => (null => (Double_A, Double_B)),
          Pre     => Double_A >= 2 and Double_B >= 2
   is
      C : Integer;
   begin
      C := 323;
      pragma Assert (Double_A * Double_B /= C);
   end RSA_Small;
   pragma Warnings (On, "* has no effect");

   pragma Warnings (Off, "* has no effect");
   procedure RSA (A, B: in Natural)
     with Depends => (null => (A, B)),
          Pre     => A >= 2 and B >= 2
   is
      C : Integer;
   begin
      C := 12166397;
      pragma Assert (A * B /= C);
   end RSA;
   pragma Warnings (On, "* has no effect");

   function Plus (A, B: Integer) return Integer
     with Pre  => A + B in Integer,  --  @OVERFLOW_CHECK:FAIL @COUNTEREXAMPLE
          Post => Plus'Result = A + B
   is
      R : Integer;
   begin
      R := A;
      if B >= 0 then
         for I in Integer range 1 .. B loop
            R := Integer'Succ (R);
            pragma Loop_Invariant (R = A + I and B = B'Loop_Entry);
         end loop;
      else
         for I in reverse Integer range B .. -1 loop
            R := Integer'Pred (R);
            pragma Loop_Invariant (R = A + I and B = B'Loop_Entry);
         end loop;
      end if;
      return R;
   end Plus;

   function Halve_A (N: in Unsigned_Byte) return Unsigned_Byte
     with Post => Halve_A'Result + Halve_A'Result = N
                    or Halve_A'Result + Halve_A'Result + 1 = N
   is
      Half_Range : constant Unsigned_Byte := Unsigned_Byte'Last / 2;
      R : Unsigned_Byte;
   begin
      pragma Assert (Half_Range + Half_Range + 1 = Unsigned_Byte'Last);
      for I in Unsigned_Byte range 0 .. Half_Range loop
         R := I;
         exit when R + R = N or (R + R) + 1 = N;
         pragma Loop_Invariant (R = I and N > R + R + 1);
      end loop;
      return R;
   end Halve_A;

   function Halve_B (N: in Unsigned_Byte) return Unsigned_Byte
     with Post => Halve_B'Result + Halve_B'Result = N  --  @POSTCONDITION:FAIL @ COUNTEREXAMPLE
                    or Halve_B'Result + Halve_B'Result + 1 = N
   is
      Half_Range : constant Unsigned_Byte := Unsigned_Byte'Last / 2;
      R : Unsigned_Byte;
   begin
      pragma Assert (Half_Range + Half_Range + 1 = Unsigned_Byte'Last);
      for I in Unsigned_Byte range 0 .. Half_Range loop
         R := I;
         exit when R + R = N or (R + R) + 1 = N;
         pragma Loop_Invariant
           (N > R + R + 1 and R in Unsigned_Byte);  --  @LOOP_INVARIANT_PRESERV:FAIL @ COUNTEREXAMPLE
      end loop;
      return R;
   end Halve_B;

   function Halve_C (N: in Unsigned_Byte) return Unsigned_Byte
     with Post => Halve_C'Result + Halve_C'Result = N
                    or Halve_C'Result + Halve_C'Result + 1 = N
   is
      Half_Range : constant Unsigned_Byte := Unsigned_Byte'Last / 2;
      R : Unsigned_Byte;
   begin
      pragma Assert (Half_Range + Half_Range + 1 = Unsigned_Byte'Last);
      for I in Unsigned_Byte range 0 .. Half_Range loop
         R := I;
         exit when R + R = N or (R + R) + 1 = N;
         pragma Loop_Invariant (R = I
                                  and N > R + R + 1
                                  and R in Unsigned_Byte);
      end loop;
      return R;
   end Halve_C;

   function Halve_D (N: in Unsigned_Byte) return Unsigned_Byte
     with Post => Halve_D'Result = N / 2
   is
      R : Unsigned_Byte;
   begin
      for I in Unsigned_Byte range 0 .. Unsigned_Byte'Last / 2
      loop
         R := I;
         exit when R + R = N or (R + R) + 1 = N;
         pragma Loop_Invariant (R = I
                                  and N > R + R + 1
                                  and R in Unsigned_Byte);
      end loop;
      return R;
   end Halve_D;

   function Abs_Test_A (N: in Integer) return Natural
     with Post => Abs_Test_A'Result = abs (N)
   is
      R : Natural;
   begin
      if N > 0 then
         R := Natural'(N);
      else
         R := Natural'(-N);  --  @OVERFLOW_CHECK:FAIL @COUNTEREXAMPLE
      end if;
      return R;
   end Abs_Test_A;

   function Abs_Test_B (N: in Integer) return Natural
     with Pre  => N /= Integer'First,
          Post => Abs_Test_B'Result = abs (N)
   is
      R : Natural;
   begin
      if N > 0 then
         R := Natural'(N);
      else
         R := Natural'(-N);
      end if;
      return R;
   end Abs_Test_B;

   function Abs_Test_C (N: in Integer) return Natural
     with Post => Abs_Test_C'Result = abs (N)
   is
   begin
      return abs (N);  --  @OVERFLOW_CHECK:FAIL @COUNTEREXAMPLE
   end Abs_Test_C;

   function Test_Mod_A (N: in Byte) return Byte
     with Post => Test_Mod_A'Result = N  --  @POSTCONDITION:FAIL
   is
   begin
      return N mod 10;
   end Test_Mod_A;

   function Test_Mod_B (N: in Byte) return Byte
     with Post => Test_Mod_B'Result = N  --  @POSTCONDITION:FAIL
   is
   begin
      return N mod (-10);
   end Test_Mod_B;

   function Test_Mod_C (A: in Byte;
                        B: in Byte)
                       return Byte
     with Pre  => B >= -10 and B <= 20 and B /= 0,
          Post => Test_Mod_C'Result = A  --  @POSTCONDITION:FAIL
   is
   begin
      return A mod B;
   end Test_Mod_C;

   --  This test is meant to guard against the special way Python
   --  implement div.
   function Test_Div_A (N: in Byte) return Byte
   is
   begin
      pragma Assert (if N < 0 then N / 10 < 0);  --  @ASSERT:FAIL @COUNTEREXAMPLE
      return N;
   end Test_Div_A;

   function Test_Rem_A (A: in Byte;
                        B: in Byte)
                       return Byte
     with Pre  => B /= 0 ,
          Post => Test_Rem_A'Result = A  --  @POSTCONDITION:FAIL
   is
   begin
      return A rem B;
   end Test_Rem_A;

   function Test_Rem_B (A: in Byte;
                        B: in Byte)
                       return Byte
     with Pre  => B /= 0,
          Post => Test_Rem_B'Result = - ((A / B) * B) + A
   is
   begin
      return A rem B;
   end Test_Rem_B;

   function Test_Rem_C (A: in Byte;
                        B: in Byte;
                        C: in Byte)
                       return Byte
     with Pre => B /= 0 and C > A and A + B in Byte  --  @OVERFLOW_CHECK:FAIL @COUNTEREXAMPLE
   is
   begin
      return (A + B) rem ((A rem B) + C);  --  @DIVISION_CHECK:FAIL
   end Test_Rem_C;

   pragma Warnings (Off, "* has no effect");
   procedure Test_Rem_D (A: in Byte)
     with Depends => (null => A),
          Pre     => A > 1 and A < 101
   is
   begin
      pragma Assert (101 rem A /= 0);
      null;
   end Test_Rem_D;
   pragma Warnings (On, "* has no effect");

   pragma Warnings (Off, "* has no effect");
   procedure Test_Rem_E (A: in Byte)
     with Depends => (null => A),
          Pre     => A > 1 and A < 100
   is
   begin
      pragma Assert (100 rem A /= 0);  --  @ASSERT:FAIL
      null;
   end Test_Rem_E;
   pragma Warnings (On, "* has no effect");

   function IsPositive (X : in Integer) return Integer
     with Post => (if X <= 0 then IsPositive'Result = 0)
                    and (if X > 0 then IsPositive'Result = 1)
   is
      type T is range Integer'First * 2 - 1 .. Integer'Last * 2;
   begin
      return Integer (T (X) - (2 * T (X) - 1) / 2);
   end IsPositive;

   function IsPositive_Wrong (X : in Integer) return Integer
     with Post =>
     (if X >= 0 then IsPositive_Wrong'Result = 0) and --  @POSTCONDITION:FAIL
        (if X < 0 then IsPositive_Wrong'Result = 1)
   is
      type T is range Integer'First * 2 - 1 .. Integer'Last * 2;
   begin
      return Integer (T (X) - (2 * T (X) - 1) / 2);
   end IsPositive_Wrong;
end Arithmetic;
