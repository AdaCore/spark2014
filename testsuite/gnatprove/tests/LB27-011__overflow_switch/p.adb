pragma SPARK_Mode (On); function P (N : Integer) return Integer is
   Result : Integer := N;
begin
   for J in 1 .. 5 loop
      pragma Loop_Invariant (Result = N ** J);
      Result := Result * N;
   end loop;
   return Result;
end P;
