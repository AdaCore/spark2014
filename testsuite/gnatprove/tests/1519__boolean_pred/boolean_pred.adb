procedure Boolean_Pred (B : Boolean) with SPARK_Mode, Pre => B is
   P : constant Boolean := Boolean'Pred (B);
begin
   pragma Assert (not P);
end Boolean_Pred;
