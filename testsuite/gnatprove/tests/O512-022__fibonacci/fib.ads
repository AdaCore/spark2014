package Fib is pragma SPARK_Mode (On);   --In total 608 VCs
   type IntArray is array (0..100) of Integer;

   --Function to use in assertions which computes nth Fibonacci number
   --F_{0} = 1, F_{1} = 1, F_{n+2} = F_{n+1} + F_{n}
   function Fibonacci (n : Natural) return Natural with
     Pre  => (n <= 23);
   --F_{23} = 28657

   --A self composed version of a procedure which computes the
   --nth Fibonacci number and stores the result in l
   procedure FibonacciSC (n1, n2, l1, l2 : in out Natural) with
     Pre  => (n1 = n2 and then l1 = l2 and then n1 <= 23),
     Post => l1 = l2;

   --Function to use in assertions which computes n!
   function Factorial (n : Natural) return Natural with
     Pre  => (n <= 7);
   --7! = 5040

   --A self composed version of a procedure which computes n! and
   --stores the result in p
   procedure FactorialSC (n1, n2 : in Natural; p1, p2 : out Natural) with
     Pre  => (n1 = n2 and then n1 <= 7),
     Post => (p1 = p2); --nope

   --A self composed version of a procedure which computes a^n and
   --stores the result in p
   procedure PowerSC (a1, a2 : in Integer; n1, n2 : in Natural; p1, p2 : out Integer) with
     Pre  => (a1 = a2 and then n1 = n2 and then
                (a1 /= 0 or else n1 /= 0) and then
                a1 ** n1 < Integer'Last),
     Post => (p1 = p2);

   --Naive self composed version of ArrayPartitionedTransfer
   procedure ArrayPartitionedTransferSC(A1, A2 : out IntArray;
                                      B1, B2, C1, C2 : in IntArray;
                                      K1, K2 : in Natural) with
     Pre  => (K1 = K2 and then A1'First <= K1 and then K1 <= A1'Last and then
                A2'First <= K2 and then K2 <= A2'Last and then
                (for all I in A1'First..K1 => B1(I) = B2(I)) and then
                (for all I in (K1+1)..A1'Last => C1(I - K1) = C2(I - K2))),
     Post => (for all I in A1'First..A1'Last => A1(I) = A2(I)); -- @POSTCONDITION:FAIL

   --SIFL informed self composition of ArrayPartitionedTransfer
   --K does not need to be duplicated and so we don't
   procedure ArrayPartitionedTransferSIFL(A1, A2 : out IntArray;
                                          B1, B2, C1, C2 : in IntArray;
                                          K : in Natural) with
     Pre  => (A1'First <= K and then K <= A1'Last and then
                (for all I in A1'First..K => B1(I) = B2(I)) and then
                (for all I in (K+1)..A1'Last => C1(I - K) = C2(I - K))),
     Post => (for all I in A1'First..A1'Last => A1(I) = A2(I)); -- @POSTCONDITION:FAIL
end Fib;
