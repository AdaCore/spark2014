with Aida.Int32;

package body Aida_Character with SPARK_Mode is

   function To_Integer (Source : in  T) return Aida.Int32.T with
     Pre  => Is_Digit (Source),
     Contract_Cases => (Source = '0' => Check_Result (To_Integer'Result, 0),
                        Source = '1' => Check_Result (To_Integer'Result, 1),
                        Source = '2' => Check_Result (To_Integer'Result, 2),
                        Source = '3' => Check_Result (To_Integer'Result, 3),
                        Source = '4' => Check_Result (To_Integer'Result, 4),
                        Source = '5' => Check_Result (To_Integer'Result, 5),
                        Source = '6' => Check_Result (To_Integer'Result, 6),
                        Source = '7' => Check_Result (To_Integer'Result, 7),
                        Source = '8' => Check_Result (To_Integer'Result, 8),
                        Source = '9' => Check_Result (To_Integer'Result, 9));

   use type Aida.Int32.T;

   function Is_Digit (C : T) return Boolean is
   begin
      return C in '0'..'9';
   end Is_Digit;

   function Check_Result (Result : Aida.Int32.T; Expected : Integer) return Boolean is (Result = Aida.Int32.T (Expected));

   function To_Integer (Source : in T) return Aida.Int32.T with
     Refined_Post => To_Integer'Result in 0..9
   is
   begin
      return Character'Pos (Character (Source)) - Character'Pos ('0');
   end To_Integer;

end Aida_Character;
