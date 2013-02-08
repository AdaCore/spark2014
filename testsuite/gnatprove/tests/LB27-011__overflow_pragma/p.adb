pragma Overflow_Mode (General => Strict, Assertions => Eliminated);

function P (N : Integer) return Integer is
   Result : Integer := N;
   pragma Overflow_Mode (General => Strict, Assertions => Eliminated);
begin
   for J in 1 .. 5 loop
      pragma Loop_Invariant (Result = N ** J);
      Result := Result * N;
   end loop;
   return Result;
end P;
