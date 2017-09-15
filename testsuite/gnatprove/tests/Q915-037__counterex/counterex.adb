procedure Counterex (V : in out Integer) with
  SPARK_Mode,
  Post => V =  --  @COUNTEREXAMPLE
          V + 10
is
begin
   case V is
      when 1 .. 100 =>
         V := 300;
      when -300 .. -30 =>
         V := 20;
      when others =>
         V := V + 10;
   end case;
end Counterex;
