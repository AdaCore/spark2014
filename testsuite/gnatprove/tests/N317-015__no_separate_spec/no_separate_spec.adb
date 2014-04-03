package body No_Separate_Spec with
  SPARK_Mode => On
is
   Maybe : Boolean := True;

   procedure Should_Inline (B : in out Boolean) is
   begin
      if not B then
         B := True;
      end if;
   end Should_Inline;

   procedure Should_Not_Inline (B : out Boolean) with
     Post => B or not B
   is
   begin
      B := Maybe;
   end Should_Not_Inline;

   procedure Should_Prove (B : out Boolean) is
   begin
      Should_Not_Inline (B);
      Should_Inline (B);
   end Should_Prove;

end No_Separate_Spec;
