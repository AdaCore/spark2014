procedure Alias with SPARK_Mode is
   function Flip (A : in out Boolean) return Boolean
      with Side_Effects, Depends => (A => A, Flip'Result => A)
   is
   begin
      A := not A;
      return A;
   end Flip;

   Y : Boolean := True;

   function Glop return Boolean with Side_Effects, Global => (In_Out => Y) is
   begin
      Y := not Y;
      return Y;
   end Glop;

begin
   Y := Flip (Y);
   Y := Glop;
end;
