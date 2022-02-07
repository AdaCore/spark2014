procedure P is
   type Int_Acc is access Integer;
   type Rec is record
     C : Int_Acc;
   end record;
   type Arr is array (Integer range <>) of Int_Acc;

   procedure Proc (X : Rec) is null;

   X : Rec := (C => new Integer'(42));
   Y : Int_Acc := new Integer'(256);
   Z : Integer;
   A : Arr(1..2);
begin
   Proc ((X with delta C => Y));

   X := Rec'(X with delta C => Y);
   pragma Assert (X.C.all = 256);

   A := Arr'(A with delta 1 => new Integer'(1));
   pragma Assert (A(1).all = 1);

end P;
