package body Fib is pragma SPARK_Mode (On);
   function Fibonacci (n : Natural) return Natural is
      a, b, t : Natural;
   begin
      a := 1;
      b := 1;
      for i in Natural range 2..n loop
         pragma Loop_Invariant (b <= a and then a <= 2 ** (i - 2));
         t := a;
         a := a + b;
         b := t;
      end loop;
      return a;
   end Fibonacci;

   procedure FibonacciSC (n1, n2, l1, l2 : in out Natural) is
      a1, a2, b1, b2, i : Natural;
      copy_n1, copy_n2 : Natural;
   begin
      copy_n1 := n1;
      copy_n2 := n2;
      a1 := 1;
      a2 := 1;
      b1 := 1;
      b2 := 1;
      i := 2;
      while(n1 > 2) loop
         pragma Loop_Invariant (a1 = Fibonacci(i) and then -- @LOOP_INVARIANT_INIT:FAIL @LOOP_INVARIANT_PRESERV:FAIL
                        b1 = Fibonacci(i - 1) and then
                        i <= 23 and then
                        n1 + i - 2 = copy_n1);
         pragma Loop_Variant (Decreases => n1);
         a1 := a1 + b1; -- @OVERFLOW_CHECK:FAIL
         b1 := a1 - b1;
         n1 := n1 - 1;
         i := i + 1;
      end loop;
      i := 2;
      while(n2 > 2) loop
         pragma Loop_Invariant (a2 = Fibonacci(i) and then  -- @LOOP_INVARIANT_INIT:FAIL @LOOP_INVARIANT_PRESERV:FAIL
                        b2 = Fibonacci(i - 1) and then
                        i <= 23 and then
                        n2 + i - 2 = copy_n2);
         pragma Loop_Variant (Decreases => n2);
         a2 := a2 + b2; -- @OVERFLOW_CHECK:FAIL
         b2 := a2 - b2;
         n2 := n2 - 1;
         i := i + 1;
      end loop;
      if(a1 > l1) then
         l1 := a1;
      else
         l1 := 0;
      end if;
      if(a2 > l2) then
         l2 := a2;
      else
         l2 := 0;
      end if;
   end FibonacciSC;

   function Factorial (n : Natural) return Natural is
      p : Natural;
   begin
      p := 1;
      for i in Natural range 2..n loop
         p := i * p; -- @OVERFLOW_CHECK:FAIL
      end loop;
      return p;
   end Factorial;

   procedure FactorialSC (n1, n2 : in Natural; p1, p2 : out Natural) is
   begin
      p1 := 1;
      for i in Natural range 2..n1 loop
         pragma Loop_Invariant (p1 = Factorial(i - 1)); -- @LOOP_INVARIANT_INIT:FAIL @LOOP_INVARIANT_PRESERV:FAIL
         p1 := i * p1; -- @OVERFLOW_CHECK:FAIL
      end loop;
      p2 := 1;
      for i in Natural range 2..n2 loop
         pragma Loop_Invariant (p2 = Factorial(i - 1)); -- @LOOP_INVARIANT_INIT:FAIL @LOOP_INVARIANT_PRESERV:FAIL
         p2 := i * p2; -- @OVERFLOW_CHECK:FAIL
      end loop;
   end FactorialSC;

   procedure PowerSC (a1, a2 : in Integer; n1, n2 : in Natural; p1, p2 : out Integer) is
      b1, b2 : Integer;
      k1, k2 : Natural;
   begin
      p1 := 1;
      b1 := a1;
      k1 := n1;
      while (k1 > 0) loop
         pragma Loop_Invariant (a1 ** n1 = p1 * (b1 ** k1) and then k1 >= 0);
         pragma Loop_Variant (Decreases => k1);
         if (k1 rem 2 = 0) then
            pragma Assert (p1 * (b1 * b1) ** (k1 / 2) = a1 ** n1);
            k1 := k1 / 2;
            b1 := b1 * b1; -- @OVERFLOW_CHECK:FAIL
         else
            pragma Assert ((p1 * b1) * (b1 ** (k1 - 1)) = a1 ** n1);
            k1 := k1 - 1;
            p1 := b1 * p1; -- @OVERFLOW_CHECK:FAIL
         end if;
      end loop;
      p2 := 1;
      b2 := a2;
      k2 := n2;
      while (k2 > 0) loop
         pragma Loop_Invariant (a2 ** n2 = p2 * (b2 ** k2) and then k1 >= 0 and then
                          p2 <= a2 ** n2 and then b2 <= a2 ** n2);  -- @LOOP_INVARIANT_INIT:FAIL
         pragma Loop_Variant (Decreases => k2);
         if (k2 rem 2 = 0) then
            pragma Assert (p2 * (b2 * b2) ** (k2 / 2) = a2 ** n2);
            k2 := k2 / 2;
            b2 := b2 * b2; -- @OVERFLOW_CHECK:FAIL
         else
            pragma Assert ((p2 * b2) * (b2 ** (k2 - 1)) = a2 ** n2
                          and then k2 >= 1);
            k2 := k2 - 1;
            p2 := b2 * p2; -- @OVERFLOW_CHECK:FAIL
         end if;
      end loop;
   end PowerSC;

   procedure ArrayPartitionedTransferSC(A1, A2 : out IntArray;
                                        B1, B2, C1, C2 : in IntArray;
                                        K1, K2 : in Natural) is
   begin
      for I in Natural range A1'First..K1 loop
         A1(I) := B1(I);
      end loop;
      for I in Natural range (K1+1)..A1'First loop
         A1(I) := C1(I - K1);
      end loop;
      for I in Natural range A2'First..K2 loop
         A2(I) := B2(I);
      end loop;
      for I in Natural range (K2+1)..A2'Last loop
         A2(I) := C2(I - K2);
      end loop;
   end ArrayPartitionedTransferSC;

   procedure ArrayPartitionedTransferSIFL(A1, A2 : out IntArray;
                                          B1, B2, C1, C2 : in IntArray;
                                          K : in Natural) is
   begin
      for I in Natural range A1'First..K loop
         A1(I) := B1(I);
      end loop;
      for I in Natural range (K+1)..A1'Last loop
         A1(I) := C1(I - K);
      end loop;
      for I in Natural range A2'First..K loop
         A2(I) := B2(I);
      end loop;
      for I in Natural range (K+1)..A2'Last loop
         A2(I) := C2(I - K);
      end loop;
   end ArrayPartitionedTransferSIFL;
end Fib;
