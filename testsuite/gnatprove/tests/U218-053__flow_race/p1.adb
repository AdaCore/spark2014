package body P1 with Refined_State => (U1 => P2.U2, S1 => P2.S2) is
   package body P2 with Refined_State => (U2 => P3.U3, S2 => P3.S3) is
      package body P3 with Refined_State => (U3 => X3, S3 => (T3A, T3B)) is
         X3 : Boolean := True;
         T3A, T3B : T3;
         task body T3 is
         begin
            X3 := not X3;
         end;
      end P3;
   end P2;
end P1;
