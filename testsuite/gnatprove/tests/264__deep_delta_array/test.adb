procedure Test with SPARK_Mode is

   type R is record
      F, G, H : Integer;
   end record;

   type My_Arr is array (Positive range <>) of R;

   procedure Test (X : in out My_Arr; I, J, K, L : Positive) with
     Pre => I in X'Range
     and then J in X'Range
     and then K in X'Range
     and then L in X'Range;

   procedure Test (X : in out My_Arr; I, J, K, L : Positive) is
      X_Old : constant My_Arr := X with Ghost;
   begin
      X (I).F := 1;
      X (J).G := 2;
      X (K).F := 3;
      X (L).H := 4;
      pragma Assert
        (X = (X_Old with delta  --@ASSERT:PASS
             (I).F => 1,
             (J).G => 2,
             (K).F => 3,
             (L).H => 4));
   end Test;

   procedure Test_Bad (X : in out My_Arr; I, J, K, L : Positive) with
     Pre => I in X'Range
     and then J in X'Range
     and then K in X'Range
     and then L in X'Range;

   procedure Test_Bad (X : in out My_Arr; I, J, K, L : Positive) is
      X_Old : constant My_Arr := X with Ghost;
   begin
      X (L).F := 1;
      X (K).G := 2;
      X (J).F := 3;
      X (I).H := 4;
      pragma Assert
        (X = (X_Old with delta  --@ASSERT:FAIL
             (I).F => 1,
             (J).G => 2,
             (K).F => 3,
             (L).H => 4));
   end Test_Bad;

begin
   null;
end Test;
