package body Loop_Unrolling with
  SPARK_Mode
is
   procedure Init (A : out Arr) is
   begin
      for J in Index loop
         A (J) := J;
      end loop;
   end Init;

   function Sum (A : Arr) return Integer is
      Result : Integer := 0;
   begin
      for J in Index loop
         Result := Result + A (J);
      end loop;
      return Result;
   end Sum;

end Loop_Unrolling;
