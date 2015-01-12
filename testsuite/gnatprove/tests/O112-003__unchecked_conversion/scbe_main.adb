with Unchecked;

procedure sCBE_Main is
   Var_A : Unchecked.Type_A;
   Var_B : Unchecked.Type_B := (others => 0);
begin
   Var_A := Unchecked.Convert_To_A (Var_B);
end sCBE_Main;
