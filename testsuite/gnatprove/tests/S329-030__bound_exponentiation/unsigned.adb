procedure Unsigned with
  SPARK_Mode
is
   type U is mod 2 ** 64;
begin
   pragma Assert (for all I in 0 .. 63 => 2 ** I in U'Range);
end Unsigned;
