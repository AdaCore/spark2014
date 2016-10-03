limited with Aida.Int32;

package Aida_Character with SPARK_Mode is

   type T is new Character;

   function Is_Digit (C : T) return Boolean with
     Contract_Cases => (C = '0' => Is_Digit'Result,
                        C = '1' => Is_Digit'Result,
                        C = '2' => Is_Digit'Result,
                        C = '3' => Is_Digit'Result,
                        C = '4' => Is_Digit'Result,
                        C = '5' => Is_Digit'Result,
                        C = '6' => Is_Digit'Result,
                        C = '7' => Is_Digit'Result,
                        C = '8' => Is_Digit'Result,
                        C = '9' => Is_Digit'Result,
                        C > '9' => Is_Digit'Result = False,
                        C < '0' => Is_Digit'Result = False);

   function Check_Result (Result : Aida.Int32.T; Expected : Integer) return Boolean with
     Pre => Expected in 0..9;

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

end Aida_Character;
