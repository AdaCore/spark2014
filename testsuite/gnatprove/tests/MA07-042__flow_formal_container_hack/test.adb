with Informal_List;
with Formal_List;

procedure Test (A : out Informal_List.T;
                B : out Informal_List.U;
                C : out Formal_List.T;
                D : out Formal_List.U)
is
   Tmp_A : Informal_List.T;
   Tmp_B : Informal_List.U;
   Tmp_C : Formal_List.T;
   Tmp_D : Formal_List.U;
begin
   A := Tmp_A; -- flow error
   B := Tmp_B; -- flow error
   --  C := Tmp_C; -- ok
   --  D := Tmp_D; -- ok
end Test;
