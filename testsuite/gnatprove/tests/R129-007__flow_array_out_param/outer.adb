procedure Outer (X : out Integer) is
   procedure Inner with Depends => (X => null, null => X), Global => (In_Out => X), Pre => True is
   begin
      X := X + 1;
   end;
begin
   X := 0;
   Inner;
end;
