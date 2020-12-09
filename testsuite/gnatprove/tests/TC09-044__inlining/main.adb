procedure Main with SPARK_Mode is

   procedure Lemma (X : Integer) is
   begin
      pragma Assert (X + 1 > X);
   end Lemma;

begin
   Lemma (Integer'(Integer'Last));
end Main;
