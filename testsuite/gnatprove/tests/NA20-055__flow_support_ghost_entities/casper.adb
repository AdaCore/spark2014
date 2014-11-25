package body Casper is
   procedure Ghost_Proc (Par : out Integer) is
   begin
      Par := G1 + G2;  --  This is legal.
   end Ghost_Proc;

   procedure P (Par : out Integer) is
      Tmp : Integer := G2 + 1  --  This is not ineffective.
        with Ghost;
   begin
      pragma Assert (Tmp > G2);
      Par := G1;
      Ghost_G1 := Tmp;  --  This is fine
   end P;
end Casper;
