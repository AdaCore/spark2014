pragma SPARK_Mode(On);

package body Scrabble is

   type Scrabble_Value_Lookup is array (Scrabble_Letter) of Scrabble_Value;
   Lookup_Table : constant Scrabble_Value_Lookup :=
     ('A' =>  1, 'B' =>  3, 'C' =>  3, 'D' =>  2,
      'E' =>  1, 'F' =>  4, 'G' =>  2, 'H' =>  4,
      'I' =>  1, 'J' =>  8, 'K' =>  5, 'L' =>  1,
      'M' =>  3, 'N' =>  1, 'O' =>  1, 'P' =>  3,
      'Q' => 10, 'R' =>  1, 'S' =>  1, 'T' =>  1,
      'U' =>  1, 'V' =>  4, 'W' =>  4, 'X' =>  8,
      'Y' =>  4, 'Z' => 10);

   function Raw_Score (Word : in Scrabble_Word) return Scrabble_Score is
      Total_Score : Scrabble_Score := 0;
   begin
      for Letter_Index in Word'Range loop
         pragma Loop_Invariant (Total_Score <= 10*(Letter_Index - Word'First));
         Total_Score := Total_Score + Lookup_Table (Word (Letter_Index));
      end loop;
      return Total_Score;
   end Raw_Score;

end Scrabble;
