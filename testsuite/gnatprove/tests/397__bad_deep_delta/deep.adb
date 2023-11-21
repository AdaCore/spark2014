pragma Extensions_Allowed (All);

package body Deep is

   procedure Test1 (X : in out A1) is
      V1 : constant Int_Acc := new Integer'(1);
      V2 : constant Int_Acc := new Integer'(2);
   begin
      X := (X with delta 1 => V1, 1 => V2);
   end Test1;

   procedure Test2 (X : in out R2) is
      V1 : constant Int_Acc := new Integer'(1);
      V2 : constant Int_Acc := new Integer'(2);
      V3 : R1 := (F => V2, G => null, L => (others => null), M => (others => null));
   begin
      X := (X with delta A.L(1) => V1, A.L(1) => V1);  --  error
      X := (X with delta A.L(1) => V1, A => V3);       --  error
      X := (X with delta A.L(1) => V1, A.M(2) => V2);  --  ok (but rejected currently)
      X := (X with delta A.L(1) => V1, E => 3);        --  ok
   end Test2;

end Deep;
