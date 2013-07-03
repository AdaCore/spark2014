package Renam is
   X : Integer := 0;
   Y : Integer renames X;
   procedure Set_X_Through_Y;
   procedure Set_X with Post => X = X'Old;
end Renam;
