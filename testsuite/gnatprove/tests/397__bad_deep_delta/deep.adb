pragma Extensions_Allowed (All);

package body Deep is

   procedure Test1 (X : in out A1) is
      V1 : constant Int_Acc := new Integer'(1);
      V2 : constant Int_Acc := new Integer'(2);
   begin
      X := (X with delta 1 => V1, 1 => V2);
   end Test1;

end Deep;
