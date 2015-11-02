with P1;
with P2;
with P3;
with P4;
with P5;
with P6;

procedure Client is
   use type P1.Normal_Record;
   use type P3.Limited_Record_With_User_Eq;
   use type P4.Array_of_Normal_Records;
   use type P6.Array_of_Limited_Records_With_User_Eq;

   X : P1.Normal_Record;
   Y : P2.Limited_Record;
   Z : P3.Limited_Record_With_User_Eq;
   A : P4.Array_Of_Normal_Records;
   B : P5.Array_Of_Limited_Records;
   C : P6.Array_of_Limited_Records_With_User_Eq;
begin
   pragma Assert (X = X);
   --  pragma Assert (Y = Y); -- invalid, no equality operator for limited type!
   pragma Assert (Z = Z);
   pragma Assert (A = A);
   --  pragma Assert (B = B); -- invalid, no equality operator for array of limited types!
   pragma Assert (C = C);
end;
