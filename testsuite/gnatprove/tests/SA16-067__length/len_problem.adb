procedure Len_Problem with SPARK_Mode is
   capacity : constant := 255;
   type Unsigned_Long is mod 2**16;
   subtype string_length is Unsigned_Long range 0 .. capacity;

   function Id (X : Positive) return Positive is (X);

   S        : String (2 ** 16 - 1 .. Id (2 ** 16 + 255)) := (others => ' ');


begin
   pragma Assert (S'Length < string_length'Last); --@ASSERT:FAIL
end Len_Problem;
