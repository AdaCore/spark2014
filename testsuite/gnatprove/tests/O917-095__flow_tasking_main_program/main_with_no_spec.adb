with P;
with PT;

procedure Main_With_No_Spec is
begin
   loop
      P.X := not P.X;
   end loop;
end;
