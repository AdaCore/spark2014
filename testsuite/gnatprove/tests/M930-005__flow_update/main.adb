with Update_Legal; use Update_Legal;

procedure Main
  with SPARK_Mode
is
   Arr : Array_T := Array_T'(others => False);
begin
   P1 (Arr);
end Main;
