package Aida.Characters is
   pragma SPARK_Mode;

   function Is_Digit (C : Character) return Boolean with
     Contract_Cases => (C = '0' => Is_Digit'Result = True,
                        C = '1' => Is_Digit'Result = True,
                        C = '2' => Is_Digit'Result = True,
                        C = '3' => Is_Digit'Result = True,
                        C = '4' => Is_Digit'Result = True,
                        C = '5' => Is_Digit'Result = True,
                        C = '6' => Is_Digit'Result = True,
                        C = '7' => Is_Digit'Result = True,
                        C = '8' => Is_Digit'Result = True,
                        C = '9' => Is_Digit'Result = True,
                        C > '9' => Is_Digit'Result = False,
                        C < '0' => Is_Digit'Result = False);

end Aida.Characters;
