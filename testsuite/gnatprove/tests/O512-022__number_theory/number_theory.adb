pragma SPARK_Mode(On);

package body Number_Theory is

   function Fibonacci(N : Fibonacci_Argument_Type) return Natural is
      Result : Natural;
      Old    : Positive;
      Oldest : Natural;
      Temp   : Natural;
   begin
      case N is
         when 0 | 1 =>
            Result := N;

         when others =>
            Oldest := 0;
            Old    := 1;
            for I in Fibonacci_Argument_Type range 2 .. N loop
               pragma Loop_Invariant(Old = Fib(I - 1) and Oldest = Fib(I - 2));

               Temp   := Oldest;
               Oldest := Old;
               Old    := Old + Temp;
            end loop;
            Result := Old;
      end case;
      return Result;
   end Fibonacci;


   function Fibonacci2(N : Fibonacci_Argument_Type) return Natural is
      Lookup_Table : constant array(Fibonacci_Argument_Type) of Natural :=
        ( 0 =>         0,  1 =>          1,  2 =>          1,  3 =>         2,
          4 =>         3,  5 =>          5,  6 =>          8,  7 =>        13,
          8 =>        21,  9 =>         34, 10 =>         55, 11 =>        89,
         12 =>       144, 13 =>        233, 14 =>        377, 15 =>       610,
         16 =>       987, 17 =>       1597, 18 =>       2584, 19 =>      4181,
         20 =>      6765, 21 =>      10946, 22 =>      17711, 23 =>     28657,
         24 =>     46368, 25 =>      75025, 26 =>     121393, 27 =>    196418,
         28 =>    317811, 29 =>     514229, 30 =>     832040, 31 =>   1346269,
         32 =>   2178309, 33 =>    3524578, 34 =>    5702887, 35 =>   9227465,
         36 =>  14930352, 37 =>   24157817, 38 =>   39088169, 39 =>  63245986,
         40 => 102334155, 41 =>  165580141, 42 =>  267914296, 43 => 433494437,
         44 => 701408733, 45 => 1134903170, 46 => 1836311903
        );
   begin
      return Lookup_Table(N);
   end Fibonacci2;

end Number_Theory;
