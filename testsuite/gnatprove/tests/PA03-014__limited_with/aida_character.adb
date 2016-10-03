with Aida.Int32;

package body Aida_Character with SPARK_Mode is

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
