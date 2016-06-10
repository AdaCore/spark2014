package body A.B with
  SPARK_Mode
is
   procedure example is
      tmp : Integer;
   begin
      DATA1 := 0;
      tmp := DATA1 + DATA2;
   end example;
end A.B;
