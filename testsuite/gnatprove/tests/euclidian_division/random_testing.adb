with Linear_Div;
with Bounded_Random;

--  Test Linear_Div using some random value
--
--  This procedure is in SPARK and calls a subprogram whose spec is in
--  SPARK but whose body isn't (Bounded_Random).

procedure Random_Testing (Result : out Boolean)
  with Post => Result
is pragma SPARK_Mode (On);
   M, N : Integer;
   Q, R : Integer;
begin
   Bounded_Random (200, M);
   Bounded_Random (100, N);
   Linear_Div (M, N + 1, Q, R);

   Result := False;
   if R <= 98 then
      Result := True;
   end if;
end Random_Testing;
