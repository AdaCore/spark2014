procedure Test_Private with SPARK_Mode is
   package Nested_1 is
      type Root is tagged record
         F : Integer;
      end record;
      type Root_P is tagged private;
      function Create (X : Integer) return Root_P;
      function Get (X : Root_P) return Integer;
   private
      type Root_P is tagged record
         F : Integer;
      end record;
      function Create (X : Integer) return Root_P is
        (F => X);
      function Get (X : Root_P) return Integer is (X.F);
   end Nested_1;
   use Nested_1;

   package Nested_2 is
      type Child is new Root with record
         G : Integer;
      end record;
      type Child_R is new Root_P with record
         G : Integer;
      end record;
      function Create (X : Integer) return Child_R is
        ((Root_P'(Create (X)) with G => X));
      type Child_P is new Root with private;
      function Create (X : Integer) return Child_P;
      function Get (X : Child_P) return Integer;
      type Child_RP is new Root_P with private;
      function Create (X : Integer) return Child_RP;
      function Get (X : Child_RP) return Integer;
   private
      type Child_P is new Root with record
         G : Integer;
      end record;
      function Create (X : Integer) return Child_P is
        (others => X);
      function Get (X : Child_P) return Integer is (X.G);
      type Child_RP is new Root_P with record
         G : Integer;
      end record;
      function Create (X : Integer) return Child_RP is
        ((Root_P'(Create (X)) with G => X));
      function Get (X : Child_RP) return Integer is (X.G);
   end Nested_2;
   use Nested_2;

   package Nested_3 is
      type Grand_Child is new Root with private;
      function Create (X : Integer) return Grand_Child;
      function Get (X : Grand_Child) return Integer;
   private
      type Grand_Child is new Child with record
         H : Integer;
      end record;
      function Create (X : Integer) return Grand_Child is
        (others => X);
      function Get (X : Grand_Child) return Integer is (X.H);
   end Nested_3;
   use Nested_3;

   procedure Test_1 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_1 (A, B : Integer; C : out Integer) is
      X : Child_R := Child_R'(Create (A));
   begin
      Root_P (X) := Create (B);
      C := Get (Root_P (X));
   end Test_1;

   procedure Test_2 (A, B : Integer; C : out Integer) with
     Depends => (C => (A, B));

   procedure Test_2 (A, B : Integer; C : out Integer) is
      X : Child_R := Child_R'(Create (A));
   begin
      Root_P (X) := Create (B);
      C := Get (X);
   end Test_2;

   procedure Test_3 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_3 (A, B : Integer; C : out Integer) is
      X : Child_P := Child_P'(Create (A));
      Y : Root := (F => B);
   begin
      Root (X) := Y;
      C := X.F;
   end Test_3;

   procedure Test_4 (A, B : Integer; C : out Integer) with
     Depends => (C => (A, B));

   procedure Test_4 (A, B : Integer; C : out Integer) is
      X : Child_P := Child_P'(Create (A));
      Y : Root := (F => B);
   begin
      Root (X) := Y;
      C := Get (X);
   end Test_4;

   procedure Test_5 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);
   --  Imprecision is expected, assignment is going through private part

   procedure Test_5 (A, B : Integer; C : out Integer) is
      X : Child_RP := Child_RP'(Create (A));
   begin
      Root_P (X) := Create (B);
      C := Get (Root_P (X));
   end Test_5;

   procedure Test_6 (A, B : Integer; C : out Integer) with
     Depends => (C => (A, B));

   procedure Test_6 (A, B : Integer; C : out Integer) is
      X : Child_RP := Child_RP'(Create (A));
   begin
      Root_P (X) := Create (B);
      C := Get (X);
   end Test_6;

   procedure Test_7 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_7 (A, B : Integer; C : out Integer) is
      X : Root_P'Class := Child_R'(Create (A));
   begin
      Root_P (X) := Create (B);
      C := Get (Root_P (X));
   end Test_7;

   procedure Test_8 (A, B : Integer; C : out Integer) with
     Depends => (C => (A, B));

   procedure Test_8 (A, B : Integer; C : out Integer) is
      X : Root_P'Class := Child_R'(Create (A));
   begin
      Root_P (X) := Create (B);
      C := Get (Child_R (X));
   end Test_8;

   procedure Test_9 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_9 (A, B : Integer; C : out Integer) is
      X : Root'Class := Child_P'(Create (A));
      Y : Root := (F => B);
   begin
      Root (X) := Y;
      C := X.F;
   end Test_9;

   procedure Test_10 (A, B : Integer; C : out Integer) with
     Depends => (C => (A, B));

   procedure Test_10 (A, B : Integer; C : out Integer) is
      X : Root'Class := Child_P'(Create (A));
      Y : Root := (F => B);
   begin
      Root (X) := Y;
      C := Get (Child_P (X));
   end Test_10;

   procedure Test_11 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);

   procedure Test_11 (A, B : Integer; C : out Integer) is
      X : Root_P'Class := Child_RP'(Create (A));
   begin
      Root_P (X) := Create (B);
      C := Get (Root_P (X));
   end Test_11;

   procedure Test_12 (A, B : Integer; C : out Integer) with
     Depends => (C => (A, B));

   procedure Test_12 (A, B : Integer; C : out Integer) is
      X : Root_P'Class := Child_RP'(Create (A));
   begin
      Root_P (X) := Create (B);
      C := Get (X);
   end Test_12;

   procedure Test_Soundness (X : out Child_RP) is
      Y : Root_P := Create (1);
   begin
      Root_P (X) := Y; --  Initialization check shall fail, the private part
                       --  of X is not entirely initialized.
   end Test_Soundness;

   procedure Set (X : out Root_P) with
     Always_Terminates,
     Global => null,
     Import;

   procedure Test_Soundness_2 (X : out Child_RP) is
   begin
      Set (Root_P (X)); --  Initialization check shall fail, the private part
                       --  of X is not entirely initialized.
   end Test_Soundness_2;

   --  Some tests with back and forth between unrelated view conversions
   --  with current visibility.

   procedure Test_Strange_1 (A, B : Integer; C : out Integer) with
     Depends => (C => (A, B));

   procedure Test_Strange_1 (A, B : Integer; C : out Integer) is
      X : Grand_Child := Create (A);
   begin
      Child (Root'Class (X)).G := B;
      C := Get (X);
   end;

   procedure Test_Strange_2 (A, B : Integer; C : out Integer) with
     Depends => (C => (A, B));

   procedure Test_Strange_2 (A, B : Integer; C : out Integer) is
      X : Grand_Child := Create (A);
      Y : Child := (others => B);
   begin
      Child (Root'Class (X)) := Y;
      C := Get (X);
   end;

   type Grand_Grand_Child is new Grand_Child with record
     I : Integer;
   end record;
   function Create (X : Integer) return Grand_Grand_Child is
     ((Grand_Child'(Create (X)) with I => X));

   procedure Test_Strange_3 (A, B : Integer; C : out Integer) with
     Depends => (C => B, null => A);
   --  Imprecision is expected, assignment is going through the extension

   procedure Test_Strange_3 (A, B : Integer; C : out Integer) is
      X : Child'Class := Child'Class (Root'Class (Grand_Grand_Child'(Create (A))));
   begin
      Grand_Grand_Child (Root'Class(X)).I := B;
      Grand_Child (Root'Class(X)) := Create (A);
      C := Grand_Grand_Child (Root'Class(X)).I;
   end;
begin
   null;
end Test_Private;
