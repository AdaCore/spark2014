procedure Test_Moved with SPARK_Mode is
   type R is record
      F, G, H : Integer;
   end record;

   type My_Arr is array (Positive range <>) of R;

   type Int_Acc is not null access all Positive;

   type R2 is record
      A : My_Arr (1 .. 100);
   end record;

   procedure Test (X : in out R2; I, J, K, L : in out Int_Acc) with
     Pre => I.all in X.A'Range
     and then J.all in X.A'Range
     and then K.all in X.A'Range
     and then L.all  in X.A'Range,
     Post => X = (X'Old with delta
                    A (I.all).F => 1,
                    A (J.all).G => 2,
                    A (K.all).F => 3,
                    A (L.all).H => 4);

   procedure Test (X : in out R2; I, J, K, L : in out Int_Acc) is
      X_Old : constant R2 := X;
   begin
      X.A (I.all).F := 1;
      X.A (J.all).G := 2;
      X.A (K.all).F := 3;
      X.A (L.all).H := 4;
      declare
         Tmp : constant Int_Acc := K;
      begin
         pragma Assert (X = (X_Old with delta
                          A (I.all).F => 1,
                          A (J.all).G => 2,
                          A (K.all).F => 3, --  Error, K is moved
                          A (L.all).H => 4));
         K := Tmp;
      end;
   end Test;
begin
   null;
end Test_Moved;
