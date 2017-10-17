package Assign_Rec is
   type Pair is record
      A, B : Integer;
   end record;
   type Rec is record
      C : Integer;
      D : Pair;
   end record;
   procedure Assign (X : out Rec; Y : in Integer);
end Assign_Rec;
