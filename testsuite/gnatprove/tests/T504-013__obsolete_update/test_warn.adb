procedure Test_Warn is
   type Nat_Arr is array (Positive range <>) of Natural;

   procedure Update (X : in out Nat_Arr; I : Positive) with
     Pre => I in X'Range,
     Post => X = X'Old'Update (I => 0)
   is
   begin
      X (I) := 0;
   end Update;

   A : Nat_Arr := (1, 2, 3, 4);
begin
   Update (A, 3);
end Test_Warn;
