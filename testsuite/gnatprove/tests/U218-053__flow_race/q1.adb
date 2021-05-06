package body Q1
  with Refined_State => (Q1_State => (Q2.Q2A, Q2.Q2B, Q2.Q2C))
is
   procedure Flip is
   begin
      Q2.Flip;
   end;

   package body Q2
     with Refined_State => (Q2A => Q3.A,
                            Q2B => Q3.B,
                            Q2C => Q3.C)
   is
      procedure Flip is
      begin
         Q3.Flip;
      end;
      --  The data races are as follows:
      --  abstract state A (by tasks T1A, T1B)
      --   which might be better reported as abstract state Q2.Q2A
      --  state X (by tasks T1A, T1B, T2A)
      --  state Y (by tasks T1A, T1B, T3A)
      --  abstract state B (by tasks T2A, T3A)
      --   which might be better reported as abstract state Q2.Q2B
      package body Q3
        with Refined_State => (A => (X,Y),
                               B => Z,
                               C => (T1A, T1B, T2A, T3A)) is
         X, Y, Z : Boolean := True;
         T1A, T1B : T1;
         T2A : T2;
         T3A : T3;
         procedure Flip is
         begin
            X := not X;
         end;
         task body T1 is
         begin
            X := not X;
            Y := not Y;
         end T1;
         task body T2 is
         begin
            X := not X;
            Z := not Z;
         end T2;
         task body T3 is
         begin
            Y := not Y;
            Z := not Z;
         end T3;
      end Q3;
   end Q2;
end Q1;
