package body Variants with
  SPARK_Mode
is
   procedure Test (X : T; Y : in out TA; Z : out TB) is
   begin
      Z := TB(Y);
      Y := TA(X);
   end Test;
end Variants;
