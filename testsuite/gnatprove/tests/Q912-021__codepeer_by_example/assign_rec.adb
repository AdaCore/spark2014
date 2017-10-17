package body Assign_Rec is
   procedure Assign (X : out Rec; Y : in Integer) is
   begin
      X.C := Y + 1;
      X.D.B := Y - 1;
   end Assign;
end Assign_Rec;
