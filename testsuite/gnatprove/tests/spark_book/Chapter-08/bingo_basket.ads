with Bingo_Numbers; use Bingo_Numbers;
package Bingo_Basket with SPARK_Mode => On is

   function Empty return Boolean;

   procedure Load   -- Load all the Bingo numbers into the basket
      with
         Post => not Empty;

   procedure Draw (Letter : out Bingo_Letter;
                   Number : out Callable_Number)
   -- Draw a random number from the basket
      with
         Pre => not Empty;

end Bingo_Basket;
