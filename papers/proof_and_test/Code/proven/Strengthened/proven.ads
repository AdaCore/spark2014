package Proven is
   function Is_Prime (N : Natural) return Boolean;
   pragma Postcondition
     (Is_Prime'Result = (for all I in 2 .. N / 2 => N mod I /= 0));
   --  Returns true if natural number N is a prime number.

   function Are_Coprime (X, Y : Natural) return Boolean;
   pragma Postcondition
     (Are_Coprime'Result = (for all I in 2 .. Integer'Min (X, Y) =>
                              X mod I /= 0 and Y mod I /= 0));
   --  Returns true if natural numbers X and Y are coprime.

   subtype Non_Zero_Natural is Natural range 1 .. 3628800;  --  10! = 3628800

   function Factorial (N : Natural) return Non_Zero_Natural;
   pragma Precondition   (N <= 10);
   pragma Contract_Cases ((N = 0  => Factorial'Result = 1,
                           N = 1  => Factorial'Result = 1,
                           others => Factorial'Result =
                                       (N * Factorial (N - 1))));
   --  Returns the factorial of a natural number N smaller or equal to 10.
end Proven;
