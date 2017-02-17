pragma SPARK_Mode(On);

package Number_Theory is

   -- Fibonacci Numbers
   --------------------

   subtype Fibonacci_Argument_Type is Integer range 0 .. 46;

   -- It can be shown that the value returned by the mathematical Fibonacci function is the
   -- integer closest to \frac{\phi^n}{\sqrt{5}} where \phi is the Golden Ratio given by
   -- (1 + \sqrt{5})/2. See:
   -- http://www-personal.umich.edu/~copyrght/image/books/Spatial%20Synthesis2/s01math55fibo.pdf
   -- Thus we should be able to assert that Fib'Result < (1.6181**N)/2.2360 + 1.0. This is
   -- needed to prove freedom from overflow in function Fibonacci when Old + Temp is computed.
   --
   function Fib(N : Fibonacci_Argument_Type) return Natural is
      (case N is
          when 0 | 1  => N,
          when others => Fib(N - 1) + Fib(N - 2))
     with
       Ghost,
       Post => Float(Fib'Result) < (1.6181**N)/2.2360 + 1.0;

   -- Returns the Nth Fibonacci number.
   function Fibonacci(N : Fibonacci_Argument_Type) return Natural
     with Post => Fibonacci'Result = Fib(N);

   -- Returns the Nth Fibonacci number.
   function Fibonacci2(N : Fibonacci_Argument_Type) return Natural
     with Post => Fibonacci2'Result = Fib(N);

end Number_Theory;
