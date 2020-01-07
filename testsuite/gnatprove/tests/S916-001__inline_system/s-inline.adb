procedure System.Inline with SPARK_Mode is

   procedure Lemma (X : Integer) is
   begin
      pragma Assert (X + 1 > X);  -- @OVERFLOW_CHECK:FAIL
   end Lemma;

begin
   Lemma (Integer'Last);
end System.Inline;
