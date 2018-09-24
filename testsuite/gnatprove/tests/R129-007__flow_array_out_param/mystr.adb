procedure Mystr (S : out String) with
  SPARK_Mode,
  Depends => (S => null)
is
begin
   S := (others => ' ');
end Mystr;
