package Rec is

  procedure P (X : Integer) with Subprogram_Variant => (Decreases => X);
end Rec;
