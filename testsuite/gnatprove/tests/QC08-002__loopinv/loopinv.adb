procedure Loopinv with SPARK_Mode is
   function Cond (I : Integer) return Boolean is (True) with
     Pre => I <= 10;
   J : Integer := 1;
begin
   while J < 10 loop
      J := J + 1;
      pragma Loop_Invariant (Cond (J));
   end loop;
end Loopinv;
