package body aggregate is
   procedure A ( X : Integer) is
      Agg : TemplatePadT;
   begin
      Agg := (1 .. 10 => 1 / X, others => X + 1);
      Agg (1) := 0;
   end A;

end aggregate;
