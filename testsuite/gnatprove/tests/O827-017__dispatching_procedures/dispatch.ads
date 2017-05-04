package Dispatch with SPARK_Mode,
  Initializes => (C1, C2, C3, A1, A2, A3, R1, R2, R3)
is
   type Nat_Array is array (Positive range <>) of Natural;
   type Mut_Rec (D : Boolean := True) is record
      I : Integer;
   end record;

   function Init (X : Integer) return Integer;
   function Init (X : Nat_Array) return Nat_Array;
   function Init (X : Mut_Rec) return Mut_Rec;

   function Id (X : Positive) return Positive is (X);
   B_Max : constant Positive := Id (100);

   C1 : Integer;
   C2 : Integer;
   C3 : Integer;
   A1 : Nat_Array (1 .. B_Max);
   A2 : Nat_Array (1 .. B_Max);
   A3 : Nat_Array (1 .. B_Max);
   R1 : Mut_Rec;
   R2 : Mut_Rec;
   R3 : Mut_Rec;

   type Root is tagged record
      I : Integer;
   end record;

   procedure P
     (X1 : in Root;
      X2 : out Root;
      X3 : in out Root;
      Y1 : in Integer;
      Y2 : out Integer;
      Y3 : in out Integer;
      Z1 : in Nat_Array;
      Z2 : out Nat_Array;
      Z3 : in out Nat_Array;
      W1 : in Mut_Rec;
      W2 : out Mut_Rec;
      W3 : in out Mut_Rec)
   with
     Global    => (Input  => (C1, A1, R1),
                   Output => (C2, A2, R2),
                   In_Out => (C3, A3, R3)),
     Pre'Class => X1.I > 0,
     Post      => X2.I = X1.I and X3.I = X3.I'Old
       and Y3 = Y3'Old and Z3 = Z3'Old and W3 = W3'Old
       and C3 = C3'Old and A3 = A3'Old and R3 = R3'Old;

   type Child is new Root with record
      J : Integer;
   end record;

   procedure P
     (X1 : in Child;
      X2 : out Child;
      X3 : in out Child;
      Y1 : in Integer;
      Y2 : out Integer;
      Y3 : in out Integer;
      Z1 : in Nat_Array;
      Z2 : out Nat_Array;
      Z3 : in out Nat_Array;
      W1 : in Mut_Rec;
      W2 : out Mut_Rec;
      W3 : in out Mut_Rec)
   with
     Global    => (Input  => (C1, A1, R1),
                   Output => (C2, A2, R2),
                   In_Out => (C3, A3, R3)),
     Post      => X2.J < 0 and X2.I = X1.I and X3.I = X3.I'Old
      and X3.J = X3.J'Old and Y3 = Y3'Old and Z3 = Z3'Old and W3 = W3'Old
      and C3 = C3'Old and A3 = A3'Old and R3 = R3'Old;
end Dispatch;
