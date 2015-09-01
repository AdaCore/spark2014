package body Aida.Characters is
   pragma SPARK_Mode;

   function Is_Digit (C : Character) return Boolean is
   begin
      return C in '0'..'9';
   end Is_Digit;

end Aida.Characters;
