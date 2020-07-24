with Loop_Types; use Loop_Types;

procedure Validate_Arr_Zero (A : Arr_T; Success : out Boolean) with
  SPARK_Mode,
  Post => Success = (for all J in A'Range => A(J) = 0)
is
begin
   for J in A'Range loop
      if A(J) /= 0 then
         Success := False;
         return;
      end if;
      pragma Loop_Invariant (for all K in A'First .. J => A(K) = 0);
   end loop;

   Success := True;
end Validate_Arr_Zero;
