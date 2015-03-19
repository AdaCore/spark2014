package body Tagged_Aggregate_With_Root with SPARK_Mode is
   procedure Use_Aggregates is
      R1 : Root;
      R2 : Root := (F1 => 1);
      C1 : Child2 := (R2 with F2 => 1);
      C2 : Child2 := (R2 with others => <>);
      C3 : Child1 := (R2 with others => <>);
      C4 : Child2 := (Root with F2 => 1);
      C5 : Child2 := (Root with others => <>);
      C6 : Child1 := (Root with others => <>);
   begin
      pragma Assert (R1.F1 = 0);
      pragma Assert (R2.F1 = 1);
      pragma Assert (C3.F1 = 1);
      pragma Assert (C6.F1 = 0);
      pragma Assert (C1 = (1, 1));
      pragma Assert (C2 = (1, 0));
      pragma Assert (C4 = (0, 1));
      pragma Assert (C5 = (0, 0));
   end Use_Aggregates;
end Tagged_Aggregate_With_Root;
