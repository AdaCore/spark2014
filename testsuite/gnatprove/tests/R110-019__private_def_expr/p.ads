package P with SPARK_Mode => On is

   function Wrong return Integer is (0) with SPARK_Mode => Off;

   type T (D : Integer := Wrong) is private;
private
   pragma SPARK_Mode (Off);

   type T (D : Integer := Wrong) is null record;
end;
