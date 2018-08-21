package body P with SPARK_Mode is

   procedure Parenthesis is
      S : String := "(patacouffin";
   begin
      pragma Assert (S (S'First .. S'First + 4) = "(((((" );
   end Parenthesis;

end P;
