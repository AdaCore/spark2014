procedure Array_Loops_Cdp with
  SPARK_Mode
is
   type Boolean_Array is array (Positive range <>) of Boolean;
   Arr : Boolean_Array (1 .. 10);
begin
   Arr := (others => False);
   for J in Arr'Range loop
      Arr(J) := not Arr(J);
      pragma Loop_Invariant (for all K in Arr'First .. J => Arr(K));
   end loop;

   Arr := (others => False);
   for J in Arr'Range loop
      Arr(J) := not Arr(J);
      pragma Loop_Invariant (for all K in Arr'First .. J => Arr(K));
      pragma Loop_Invariant (for all K in J + 1 .. Arr'Last => not Arr(K));
   end loop;
end Array_Loops_Cdp;
