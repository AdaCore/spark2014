package body Deep is

   procedure Test1 (X : in out R2) is
      V1 : constant Int_Acc := new Integer'(1);
      V2 : constant Int_Acc := new Integer'(2);
   begin
      X := (A => (X.A with delta F => V1),
            B => (X.B with delta G => V2));
   end Test1;

end Deep;
