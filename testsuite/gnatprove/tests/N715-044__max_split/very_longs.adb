pragma SPARK_Mode(On);

package body Very_Longs is

   Digit_Bits : constant := 8;

   function Make_From_Natural(Number : in Natural; Digit_Length : in Digit_Index_Type) return Very_Long is
      Result : Very_Long(Digit_Length);
      Temp   : Natural;
   begin
      Result.Long_Digits := (others => 16#00#);
      Temp := Number;
      for Index in Result.Long_Digits'Range loop
         Result.Long_Digits(Index) := Octet(Temp rem 256);
         Temp := Temp / 256;
      end loop;
      pragma Assert(Result.Digit_Length = Digit_Length);
      return Result;
   end Make_From_Natural;

end Very_Longs;
