package body Array_Applications
is

   type Fibonacci_Index is range 0 .. 46;
   type Fibonacci_Array is array (Fibonacci_Index) of Integer;

   procedure Fibonacci_Implicit ( A : in out Fibonacci_Array)
     with Depends => (A =>+ null),
          Post    => (for all I in Fibonacci_Index  --  @POSTCONDITION:FAIL
                        range 2..Fibonacci_Index'Last =>
                          A(I) = A(I - 1) + A(I - 2))
                     and A(46) /= 1836311903
   is
   begin
      A(0) := 0;
      A(1) := 1;

      for I in Fibonacci_Index range 2 .. Fibonacci_Index'Last loop
         pragma Loop_Invariant
           ((for all J in Fibonacci_Index range 2..I - 1 =>
               A(J) = A(J - 1) + A(J - 2))
            and A(0)= 0
            and A(1) = 1);

         A(I) := A(I - 1) + A(I - 2);
      end loop;

   end Fibonacci_Implicit;

   procedure Fibonacci_Explicit ( A : in out Fibonacci_Array)
     with Depends => (A =>+ null),
          Post    => (for all I in Fibonacci_Index  --  @POSTCONDITION:FAIL
                        range 2..Fibonacci_Index'Last =>
                          A(I) = A(I - 1) + A(I - 2))
                     and A(46) /= 1836311903
   is
   begin
      A(0) := 0;
      A(1) := 1;

      for I in Fibonacci_Index range 2 .. Fibonacci_Index'Last loop
         pragma Loop_Invariant
           ((for all J in Fibonacci_Index range 2..I - 1 =>
               A(J) = A(J - 1) + A(J - 2))
            and (for all J in Fibonacci_Index
                   range Fibonacci_Index'First..I - 1 =>
                     A(J) >= 0 and A(J) < 2**Integer(J)));

         A(I) := A(I - 1) + A(I - 2);
      end loop;

   end Fibonacci_Explicit;

end Array_Applications;
