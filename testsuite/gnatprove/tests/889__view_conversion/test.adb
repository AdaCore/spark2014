procedure Test with SPARK_Mode is
   type Root is tagged record
      F : Integer;
   end record;

   type Child is new Root with record
      G : Integer;
   end record;

   procedure Test (A, B : Integer; C : out Integer) with
     Depends => (C => A, null => B);

   procedure Test (A, B : Integer; C : out Integer) is
      X : Child := (A, A);
   begin
      X.G := B;
      C := Child (X).F;
   end Test;

   procedure Test_2 (A, B : Integer; C : out Integer) with
     Depends => (C => A, null => B);

   procedure Test_2 (A, B : Integer; C : out Integer) is
      X : Child := (A, A);
   begin
      X.G := B;
      C := Root (X).F;
   end Test_2;

   procedure Test_3 (A, B : Integer; C : out Integer) with
     Depends => (C => A, null => B);

   procedure Test_3 (A, B : Integer; C : out Integer) is
      X : Root'Class := Child'(A, A);
   begin
      Child (X).G := B;
      C := Child (X).F;
   end Test_3;

   procedure Test_4 (A, B : Integer; C : out Integer) with
     Depends => (C => A, null => B);

   procedure Test_4 (A, B : Integer; C : out Integer) is
      X : Root'Class := Child'(A, A);
   begin
      Child (X).G := B;
      C := Root (X).F;
   end Test_4;

   procedure Test_5 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_5 (A, B : Integer; C : out Integer) is
      X : Child := (A, A);
   begin
      X.G := B;
      C := Child (X).G;
   end Test_5;

   procedure Test_6 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);
   --  Imprecision is expected, going through the extension

   procedure Test_6 (A, B : Integer; C : out Integer) is
      X : Root'Class := Child'(A, A);
   begin
      Child (X).G := B;
      C := Child (X).G;
   end Test_6;

   procedure Test_7 (A, B : Integer; C : out Integer) with
     Depends => (C => A, null => B);

   procedure Test_7 (A, B : Integer; C : out Integer) is
      X : Child := (A, A);
   begin
      C := Child ((X with delta G => B)).F;
   end Test_7;

   procedure Test_8 (A, B : Integer; C : out Integer) with
     Depends => (C => A, null => B);

   procedure Test_8 (A, B : Integer; C : out Integer) is
      X : Child := (A, A);
   begin
      C := Root ((X with delta G => B)).F;
   end Test_8;

   procedure Test_9 (A, B : Integer; C : out Integer) with
     Depends => (C => A, null => B);

   procedure Test_9 (A, B : Integer; C : out Integer) is
      X : Root'Class := Child'(A, A);
   begin
      C := Child ((Child (X) with delta G => B)).F;
   end Test_9;

   procedure Test_10 (A, B : Integer; C : out Integer) with
     Depends => (C => A, null => B);

   procedure Test_10 (A, B : Integer; C : out Integer) is
      X : Root'Class := Child'(A, A);
   begin
      C := Root ((Child (X) with delta G => B)).F;
   end Test_10;

   procedure Test_11 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_11 (A, B : Integer; C : out Integer) is
      X : Child := (A, A);
   begin
      C := Child ((X with delta G => B)).G;
   end Test_11;

   procedure Test_12 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_12 (A, B : Integer; C : out Integer) is
      X : Root'Class := Child'(A, A);
   begin
      C := Child ((Child (X) with delta G => B)).G;
   end Test_12;
begin
   null;
end Test;
