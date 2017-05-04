with Dispatch; use Dispatch;
procedure Call_Dispatch with SPARK_Mode is
   X1 : Root'Class := Root'(I => 1);
   X2 : Root'Class := Root'(I => 2);
   X3 : Root'Class := Root'(I => 3);
   V1 : Root'Class := Child'(I => 1, J => 1);
   V2 : Root'Class := Child'(I => 2, J => 2);
   V3 : Root'Class := Child'(I => 3, J => 3);
   Y1 : Integer := Init (C1);
   Y2 : Integer;
   Y3 : Integer := Init (C3);
   Z1 : Nat_Array := Init (A1);
   Z2 : Nat_Array := Init (A2);
   Z3 : Nat_Array := Init (A3);
   W1 : Mut_Rec := Init (R1);
   W2 : Mut_Rec := Init (R2);
   W3 : Mut_Rec := Init (R3);
begin
   P (X1, X2, X3, Y1, Y2, Y3, Z1, Z2, Z3, W1, W2, W3);
   pragma Assert (X2.I = X1.I);
   pragma Assert (X3.I = 3);
   P (V1, V2, V3, Y1, Y2, Y3, Z1, Z2, Z3, W1, W2, W3);
   pragma Assert (V2.I = V1.I);
   pragma Assert (V3.I = 3);
   pragma Assert (Child (V2).J < 0);
   pragma Assert (Child (V3).J = 3);
end Call_Dispatch;
