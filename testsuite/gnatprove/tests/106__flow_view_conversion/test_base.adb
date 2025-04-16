procedure Test_Base with SPARK_Mode is
   type Root is tagged record
      F : Integer;
      I : Integer;
   end record;
   type Child is new Root with record
      G : Integer;
      J : Integer;
   end record;

   procedure Test_1 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);
   --  Imprecision is expected, assignment is going through the extension

   procedure Test_1 (A, B : Integer; C : out Integer) is
      X : Root'Class := Root'Class (Child'(A, A, A, A));
   begin
      Child'Class (X).G := B;
      C := Child'Class (X).G;
   end Test_1;

   procedure Test_2 (A, B : Integer; C : out Integer) with
     Depends => (C => A, null => B);

   procedure Test_2 (A, B : Integer; C : out Integer) is
      X : Root'Class := Root'Class (Child'(A, A, A, A));
   begin
      Child'Class (X).G := B;
      C := X.F;
   end Test_2;

   procedure Test_3 (A, B : Integer; C : out Integer) with
     Depends => (C => A, null => B);

   procedure Test_3 (A, B : Integer; C : out Integer) is
      X : Child'Class := Child'(A, A, A, A);
      Y : Child'Class := Child'(B, B, B, B);
   begin
      Root (X) := Root (Y);
      C := X.G;
   end Test_3;

   procedure Test_4 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_4 (A, B : Integer; C : out Integer) is
      X : Child'Class := Child'(A, A, A, A);
      Y : Child'Class := Child'(B, B, B, B);
   begin
      Root (X) := Root (Y);
      C := X.F;
   end Test_4;

   procedure Test_5 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_5 (A, B : Integer; C : out Integer) is
      X : Child'Class := Child'(A, A, A, A);
      Y : Child'Class := Child'(B, B, B, B);
   begin
      Root'Class (X) := Root'Class (Y);
      C := X.G;
   end Test_5;

   procedure Test_6 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_6 (A, B : Integer; C : out Integer) is
      X : Child'Class := Child'(A, A, A, A);
      Y : Child'Class := Child'(B, B, B, B);
   begin
      Root'Class (X) := Root'Class (Y);
      C := X.F;
   end Test_6;

   procedure Test_7 (A, B : Integer; C : out Integer) with
     Depends => (C => A, null => B);

   procedure Test_7 (A, B : Integer; C : out Integer) is
      X : Root'Class := Root'Class (Child'(A, A, A, A));
      Y : Child'Class := Child'(B, B, B, B);
   begin
      Root (X) := Root (Y);
      C := Child'Class (X).G;
   end Test_7;

   procedure Test_8 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_8 (A, B : Integer; C : out Integer) is
      X : Root'Class := Root'Class (Child'(A, A, A, A));
      Y : Child'Class := Child'(B, B, B, B);
   begin
      Root (X) := Root (Y);
      C := X.F;
   end Test_8;

   procedure Test_9 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_9 (A, B : Integer; C : out Integer) is
      X : Root'Class := Root'Class (Child'(A, A, A, A));
      Y : Child'Class := Child'(B, B, B, B);
   begin
      Root'Class (X) := Root'Class (Y);
      C := Child'Class (X).G;
   end Test_9;

   procedure Test_10 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_10 (A, B : Integer; C : out Integer) is
      X : Root'Class := Root'Class (Child'(A, A, A, A));
      Y : Child'Class := Child'(B, B, B, B);
   begin
      Root'Class (X) := Root'Class (Y);
      C := X.F;
   end Test_10;

   procedure Test_Soundness (X : out Root'Class);

   procedure Test_Soundness (X : out Root'Class) is
      Y : Child := Child'(others => 1);
   begin
      Child (X) := Y; --  Initialization check shall fail, the extension of X
                      --  is not entirely initialized.
   end Test_Soundness;

   procedure Test_Soundness_2 (X : out Root) with Extensions_Visible;

   procedure Test_Soundness_2 (X : out Root) is
      Y : Child := Child'(others => 1);
   begin
      Child (Root'Class (X)) := Y; --  Initialization check shall fail, the extension of X
                      --  is not entirely initialized.
   end Test_Soundness_2;

begin
   null;
end;
