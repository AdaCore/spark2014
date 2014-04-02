package body No_Separate_Spec with
  SPARK_Mode => On
is
   procedure Should_Inline (B : out Boolean) is
   begin
      B := True;
   end Should_Inline;

   procedure Should_Prove (B : out Boolean) is
   begin
      Should_Inline (B);
   end Should_Prove;

end No_Separate_Spec;
