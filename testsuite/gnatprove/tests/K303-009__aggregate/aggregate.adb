package body aggregate is
   procedure A ( X : Integer; K : out TemplatePadT) is
      Agg : TemplatePadT;
   begin
      Agg := (1 .. 10 => 1 / X, others => X + 1);
      Agg (1) := Agg (1) + 1;
      K := Agg;
   end A;

end aggregate;
