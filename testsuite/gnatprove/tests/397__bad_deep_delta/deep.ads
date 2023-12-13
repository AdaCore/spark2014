package Deep is

   type Int_Acc is access Positive;

   type A1 is array (1 .. 5) of Int_Acc;

   procedure Test1 (X : in out A1) with
     Pre => (for all J in X'Range => X(J) = null),
     Post => X(1).all = 2;

end Deep;
