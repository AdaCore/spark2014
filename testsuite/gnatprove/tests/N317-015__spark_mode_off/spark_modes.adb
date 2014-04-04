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

   procedure Should_Not_Inline_Bis (B : out Boolean);

   procedure Should_Not_Inline_Bis (B : out Boolean) is
      pragma SPARK_Mode (Off);
   begin
      B := True;
   end Should_Not_Inline_Bis;

   procedure Should_Not_Prove (B : in out Boolean) is
   begin
      if B then
         Should_Not_Inline (B);
      else
         Should_Not_Inline_Bis (B);
      end if;
   end Should_Not_Prove;

end SPARK_Modes;
