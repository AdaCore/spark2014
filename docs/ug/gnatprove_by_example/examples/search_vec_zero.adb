with Loop_Types; use Loop_Types; use Loop_Types.Vectors;

procedure Search_Vec_Zero (V : Vec_T; Pos : out Opt_Index_T; Success : out Boolean) with
  SPARK_Mode,
  Post => Success = (for some J in First_Index (V) .. Last_Index (V) => Element (V, J) = 0) and then
          (if Success then Element (V, Pos) = 0)
is
begin
   for J in First_Index (V) .. Last_Index (V) loop
      if Element (V, J) = 0 then
         Success := True;
         Pos := J;
         return;
      end if;
      pragma Loop_Invariant (for all K in First_Index (V) .. J => Element (V, K) /= 0);
   end loop;

   Success := False;
   Pos := 0;
end Search_Vec_Zero;
