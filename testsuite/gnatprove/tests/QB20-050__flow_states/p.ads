package P with Abstract_State => SP, Initializes => SP is
private
   package Q with Abstract_State => (SQ with Part_Of => SP), Initializes => SQ is
   private
      package R with Abstract_State => (SR with Part_Of => SQ), Initializes => SR is
      private
         procedure Flip with Global => (Proof_In => SP);
      end;
   end;
end;
