package body R1 with SPARK_Mode,
  Refined_State => (S1 => R2.S2, U1 => R2.U2)
is
   package body R2 with
     Refined_State => (S2 => (TO2A, TO2B, R3.S3), U2 => R3.U3)
   is
      TO2A, TO2B : TT2;
      package body R3 with
        Refined_State => (S3 => null, U3 => R3.X3)
      is
         X3 : Boolean := True;
         procedure Flip with Refined_Global => (In_Out => X3) is
         begin
            X3 := not X3;
         end Flip;
      end R3;

      task body TT2 is
      begin
         loop
            R3.Flip;
         end loop;
      end TT2;
   end R2;
end R1;
