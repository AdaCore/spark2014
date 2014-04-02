package body SPARK_Modes with
  SPARK_Mode => On
is
   procedure Should_Not_Inline (B : out Boolean);

   procedure Should_Not_Inline (B : out Boolean) with
     SPARK_Mode => Off
   is
   begin
      B := True;
   end Should_Not_Inline;

   procedure Should_Not_Prove (B : out Boolean) is
   begin
      Should_Not_Inline (B);
   end Should_Not_Prove;

end SPARK_Modes;
