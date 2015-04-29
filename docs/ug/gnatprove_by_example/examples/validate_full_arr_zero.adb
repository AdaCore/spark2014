with Loop_Types; use Loop_Types;

procedure Validate_Full_Arr_Zero (A : Arr_T; Success : out Boolean) with
  SPARK_Mode,
  Post => Success = (for all J in A'Range => A(J) = 0)
is
begin
   Success := True;

   for J in A'Range loop
      if A(J) /= 0 then
         Success := False;
         --  perform some logging here instead of returning
      end if;
      pragma Loop_Invariant (Success = (for all K in A'First .. J => A(K) = 0));
   end loop;
end Validate_Full_Arr_Zero;
