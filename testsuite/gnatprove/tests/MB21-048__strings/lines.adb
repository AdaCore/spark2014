package body Lines is
   pragma SPARK_Mode(On);
   function Last_Lines
     (S : String; Size : Positive) return String
   is
      Pos : Natural;
   begin
      Pos := Size;
      return S (1 .. Pos);
   end Last_Lines;
end Lines;
