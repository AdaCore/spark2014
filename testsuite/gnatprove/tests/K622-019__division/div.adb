procedure Div (X, Y : Integer; Z : out Integer) is
begin
   if Y /= 0 and then
     (X /= Integer'First or else Y /= -1)
   then
      Z := X / Y;
   else
      Z := Integer'First;
   end if;
end Div;
