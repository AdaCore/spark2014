with Ada.Numerics.Discrete_Random;
package body Bingo_Basket.Random with SPARK_Mode => Off is

   package Random_Bingo is new Ada.Numerics.Discrete_Random
                               (Result_Subtype => Callable_Number);

   -- The following object holds the state of a random Bingo number generator
   Bingo_Gen : Random_Bingo.Generator;

   function Random_Number return Callable_Number is
   begin
      return Random_Bingo.Random (Gen => Bingo_Gen);
   end Random_Number;

begin
   -- Initialize the random number generator from the system clock
   Random_Bingo.Reset (Gen => Bingo_Gen);
end Bingo_Basket.Random;
