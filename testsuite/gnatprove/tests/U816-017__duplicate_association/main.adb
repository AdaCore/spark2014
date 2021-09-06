with Interfaces; use Interfaces;
procedure Main with SPARK_Mode is
   type Int_Acc is access Integer;
   type C_Int_Acc is access constant Integer;

   type Int_Acc_Arr is array (1 .. 10) of Int_Acc;

   type Rec is record
      X, Y: Int_Acc;
      Z   : C_Int_Acc;
      A   : Int_Acc_Arr;
   end record;

   type Rec_Acc is access Rec;

   type Arr is array (1 .. 10) of Rec_Acc;

   function F return Rec with Import;

   R : Rec;
   X : Int_Acc := new Integer'(15);
   Y : C_Int_Acc := new Integer'(15);

   --  Examples that should be accepted
   A1 : Arr := (others => null);
   A2 : Arr := (others => new Rec);
   A3 : Arr := (others => new Rec'(new Integer'(14), null, Y, (others => null)));
   A4 : Arr := (for I in 1 .. 10 => new Rec'(X => new Integer'(I), Y => null, Z => Y, A => (for I in 1 .. 10 => new Integer'(12))));
   A5 : Arr := (others => new Rec'(Z => Y, A => (for I in others => new Integer'(12)), others => new Integer'(14)));
   A6 : Arr := (others => new Rec'(F));

   --  Examples that should be rejected
   B2 : Arr := (others => new Rec'(R));
   B3 : Arr := (others => new Rec'(X, null, Z => Y, A => (others => null)));
   B4 : Arr := (for I in 1 .. 10 => new Rec'(X => X, Y => null, Z => Y, A => (others => null)));
   B5 : Arr := (others => new Rec'(Z => Y, A => (others => null), others => X));
   B6 : Arr := (others => new Rec'(R with delta X => new Integer'(14)));
   B7 : Arr := (others => new Rec'(Z => Y, A => (others => X), others => null));
begin
  null;
end;
