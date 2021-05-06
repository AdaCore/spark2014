package P1 with Abstract_State => (U1, S1) is
private
   package P2 with Abstract_State => ((U2 with Part_Of => P1.U1), (S2 with Part_Of => P1.S1)) is
   private
      package P3 with Abstract_State => ((U3 with Part_Of => P2.U2), (S3 with Part_Of => P2.S2)) is
         task type T3;
      end;
   end P2;
end P1;
