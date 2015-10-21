--  The original purpose of this test was to highlight inductive reasoning.
--  There are two versions of this, implicit and explicit; the latter
--  adding some bounds on the values on the array that do not require
--  inductive reasoning (but does require support for **).

package body Array_Applications
is

   type Fibonacci_Index is range 0 .. 30;
   type Fibonacci_Array is array (Fibonacci_Index) of Natural;

   --  A(30) is actually 832040
   procedure Fibonacci_Implicit ( A : in out Fibonacci_Array)
   with Global  => null,
        Depends => (A =>+ null),
        Post    => A(30) /= 832040 -- @POSTCONDITION:FAIL
   is
   begin
      A(0) := 0;
      A(1) := 1;

      for I in Fibonacci_Index range 2 .. Fibonacci_Index'Last loop
         A(I) := A(I - 1) + A(I - 2);

         pragma Loop_Invariant
           ((for all J in Fibonacci_Index range 2 .. I =>
               A(J) = A(J - 1) + A(J - 2))
            and A(0) = 0
            and A(1) = 1);
      end loop;
   end Fibonacci_Implicit;

   procedure Fibonacci_Implicit_OK ( A : in out Fibonacci_Array)
   with Global  => null,
        Depends => (A =>+ null),
        Post    => A(30) = 832040 -- POSTCONDITION:PASS
   is
   begin
      A(0) := 0;
      A(1) := 1;

      for I in Fibonacci_Index range 2 .. Fibonacci_Index'Last loop
         A(I) := A(I - 1) + A(I - 2);

         pragma Loop_Invariant
           ((for all J in Fibonacci_Index range 2 .. I =>
               A(J) = A(J - 1) + A(J - 2))
            and A(0) = 0
            and A(1) = 1);
      end loop;
   end Fibonacci_Implicit_OK;

   --  To make overflow checking for the addition easier we can put
   --  explicit bounds on the array that depend on the index only.
   --  Fibonacci (n) grows slower than 2^n, and that is sufficient to show
   --  we would not overflow.

   --  A(30) is actually 832040
   procedure Fibonacci_Explicit ( A : in out Fibonacci_Array)
   with Global => null,
        Depends => (A =>+ null),
        Post    => A(30) /= 832040 -- @POSTCONDITION:FAIL
   is
   begin
      A(0) := 0;
      A(1) := 1;

      for I in Fibonacci_Index range 2 .. Fibonacci_Index'Last loop
         A(I) := A(I - 1) + A(I - 2);
         pragma Loop_Invariant
           (A(0) = 0 and
            A(1) = 1 and
            (for all J in Fibonacci_Index range 2 .. I =>
               A(J) = A(J - 1) + A(J - 2)) and
            (for all J in Fibonacci_Index range Fibonacci_Index'First .. I =>
               A(J) >= 0 and A(J) < 2**Natural(J)));
      end loop;
   end Fibonacci_Explicit;

   procedure Fibonacci_Explicit_OK ( A : in out Fibonacci_Array)
   with Global  => null,
        Depends => (A =>+ null),
        Post    => A(30) = 832040 -- POSTCONDITION:PASS
   is
   begin
      A(0) := 0;
      A(1) := 1;

      for I in Fibonacci_Index range 2 .. Fibonacci_Index'Last loop
         A(I) := A(I - 1) + A(I - 2);
         pragma Loop_Invariant
           (A(0) = 0 and
            A(1) = 1 and
            (for all J in Fibonacci_Index range 2 .. I =>
               A(J) = A(J - 1) + A(J - 2)) and
            (for all J in Fibonacci_Index range Fibonacci_Index'First .. I =>
               A(J) >= 0 and A(J) < 2**Natural(J)));
      end loop;
   end Fibonacci_Explicit_OK;

end Array_Applications;
