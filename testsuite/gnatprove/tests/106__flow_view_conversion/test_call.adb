procedure Test_Call with SPARK_Mode is
   type Root is tagged record
      F : Integer;
      I : Integer;
   end record;
   type Child is new Root with record
      G : Integer;
      J : Integer;
   end record;

   procedure Set (X : out Root; Y : Integer) with
     Always_Terminates,
     Global => null,
     Import;

   procedure Set_Ext (X : out Root; Y : Integer) with
     Extensions_Visible,
     Always_Terminates,
     Global => null,
     Import;

   procedure Set_Class (X : out Root'Class; Y : Integer) with
     Always_Terminates,
     Global => null,
     Import;

   procedure Test_1 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_1 (A, B : Integer; C : out Integer) is
      X : Root'Class := Root'(A, A);
   begin
      Set (Root (X), B);
      C := X.F;
   end Test_1;

   procedure Test_2 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_2 (A, B : Integer; C : out Integer) is
      X : Root'Class := Root'(A, A);
   begin
      Set_Ext (Root (X), B);
      C := X.F;
   end Test_2;

   procedure Test_3 (A, B : Integer; C : out Integer) with
     Depends => (C => A, null => B);

   procedure Test_3 (A, B : Integer; C : out Integer) is
      X : Child'Class := Child'(A, A, A, A);
   begin
      Set (Root (X), B);
      C := X.G;
   end Test_3;

   procedure Test_4 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_4 (A, B : Integer; C : out Integer) is
      X : Child'Class := Child'(A, A, A, A);
   begin
      Set (Root (X), B);
      C := X.F;
   end Test_4;

   procedure Test_5 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_5 (A, B : Integer; C : out Integer) is
      X : Child'Class := Child'(A, A, A, A);
   begin
      Set_Ext (Root (X), B);
      C := Child'Class (X).G;
   end Test_5;

   procedure Test_6 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_6 (A, B : Integer; C : out Integer) is
      X : Child'Class := Child'(A, A, A, A);
   begin
      Set_Ext (Root (X), B);
      C := X.F;
   end Test_6;

   procedure Test_7 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_7 (A, B : Integer; C : out Integer) is
      X : Child'Class := Child'(A, A, A, A);
   begin
      Set_Class (Root (X), B);
      C := Child'Class (X).G;
   end Test_7;

   procedure Test_8 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_8 (A, B : Integer; C : out Integer) is
      X : Child'Class := Child'(A, A, A, A);
   begin
      Set_Class (Root (X), B);
      C := X.F;
   end Test_8;

   procedure Set (X : out Child) with
     Always_Terminates,
     Global => null,
     Import;

   procedure Test_Soundness (X : out Root'Class);

   procedure Test_Soundness (X : out Root'Class) is
   begin
      Set (Child (X)); --  Initialization check shall fail, the extension of X
                      --  is not entirely initialized.
   end Test_Soundness;

   procedure Test_Soundness_2 (X : out Root) with Extensions_Visible;

   procedure Test_Soundness_2 (X : out Root) is
   begin
      Set (Child (Root'Class (X))); --  Initialization check shall fail, the extension of X
                      --  is not entirely initialized.
   end Test_Soundness_2;

begin
   null;
end Test_Call;
