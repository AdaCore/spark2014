package Q1 with Abstract_State => (Q1_State) is
   procedure Flip with Global => (In_Out => Q1_State);
   private
      package Q2
        with Abstract_State => ((Q2A with Part_Of => Q1.Q1_State),
                                (Q2B with Part_Of => Q1.Q1_State),
                                (Q2C with Part_Of => Q1.Q1_State)) is
         procedure Flip;
         private
            package Q3
              with Abstract_State => ((A with Part_Of => Q2A),
                                      (B with Part_Of => Q2B),
                                      (C with Part_Of => Q2C)) is
               procedure Flip;
               task type T1;
               task type T2;
               task type T3;
            end Q3;
      end Q2;
end Q1;
