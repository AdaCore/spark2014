package body Alias
  with SPARK_Mode
is
   procedure P (X : in out Integer) is
   begin
      X := G + X;
   end P;
   procedure Q (X : Integer) is
   begin
      G := G + X;
   end Q;

   procedure P (X : in out R) is
   begin
      X.F := H.F + X.F;
   end P;
   procedure Q (X : R) is
   begin
      H.F := H.F + X.F;
   end Q;

   procedure P (X : in out A) is
   begin
      X (1) := I (1) + X (1);
   end P;
   procedure Q (X : A) is
   begin
      I (1) := I (1) + X (1);
   end Q;

   procedure P (X : in out B) is
   begin
      X (1) := J (1) + X (1);
   end P;
   procedure Q (X : B) is
   begin
      J (1) := J (1) + X (1);
   end Q;

   procedure Test is
   begin
      P (G);
      Q (G);
      P (H);
      Q (H);
      P (I);
      Q (I);
      P (J);
      Q (J);
   end Test;
end Alias;
