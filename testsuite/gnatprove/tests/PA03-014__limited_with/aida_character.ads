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

end Aida_Character;
