procedure Repr with SPARK_Mode is
   function My_Prop (D1, D2, D3: Boolean) return Boolean is (D1 and D2 and
D3);
   procedure P (D1, D2, D3, D4, D5: in out Boolean) with
     Pre  => D2 and D4 and D5,
     Post => D1
     and then D2
     and then My_Prop (D3, D4, D5)
   is
   begin
      D1 := True;
   end P;
begin
   null;
end Repr;
