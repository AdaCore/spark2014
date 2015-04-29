with Loop_Types; use Loop_Types;

procedure Search_Arr_Zero (A : Arr_T; Pos : out Opt_Index_T; Success : out Boolean) with
  SPARK_Mode,
  Post => Success = (for some J in A'Range => A(J) = 0) and then
          (if Success then A (Pos) = 0)
is
begin
   for J in A'Range loop
      if A(J) = 0 then
         Success := True;
         Pos := J;
         return;
      end if;
      pragma Loop_Invariant (for all K in A'First .. J => A(K) /= 0);
   end loop;

   Success := False;
   Pos := 0;
end Search_Arr_Zero;
