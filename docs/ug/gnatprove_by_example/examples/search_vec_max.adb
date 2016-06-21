with Loop_Types; use Loop_Types; use Loop_Types.Vectors;

procedure Search_Vec_Max (V : Vec_T; Pos : out Index_T; Max : out Component_T) with
  SPARK_Mode,
  Pre  => not Is_Empty (V),
  Post => (for all J in First_Index (V) .. Last_Index (V) => Element (V, J) <= Max) and then
          (for some J in First_Index (V) .. Last_Index (V) => Element (V, J) = Max) and then
          Pos in First_Index (V) .. Last_Index (V) and then
          Element (V, Pos) = Max
is
begin
   Max := 0;
   Pos := First_Index (V);

   for J in First_Index (V) .. Last_Index (V) loop
      if Element (V, J) > Max then
         Max := Element (V, J);
         Pos := J;
      end if;
      pragma Loop_Invariant (for all K in First_Index (V) .. J => Element (V, K) <= Max);
      pragma Loop_Invariant (for some K in First_Index (V) .. J => Element (V, K) = Max);
      pragma Loop_Invariant (Pos in First_Index (V) .. J);
      pragma Loop_Invariant (Element (V, Pos) = Max);
   end loop;
end Search_Vec_Max;
