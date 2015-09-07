pragma SPARK_Mode(On);
package Scrabble is

   subtype Scrabble_Letter is Character range 'A' .. 'Z';

   subtype Scrabble_Value is Positive
      with Static_Predicate => Scrabble_Value in 1 .. 5 | 8 | 10;

   type Scrabble_Word is array(Positive range <>) of Scrabble_Letter;

   subtype Scrabble_Score is Natural range 0 .. 100;
   function Raw_Score (Word : in Scrabble_Word) return Scrabble_Score
      with Pre => (Word'Length <= 10);

end Scrabble;
