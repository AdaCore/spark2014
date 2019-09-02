procedure System.Incr (X : in out Integer) with SPARK_Mode is
   procedure Prove_Not_To_Big with Ghost,
     Post => X < Integer'Last
   is
   begin
      null;
   end Prove_Not_To_Big;
begin
   Prove_Not_To_Big;
   X := X + 1;
end System.Incr;
