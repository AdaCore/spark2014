with Assign_Rec; use Assign_Rec;
procedure Bad_Assign_Rec (X : out Rec; Y : in Integer) is
begin
   X.C := Y * 1_000_000;
   X.D.B := Y / 1_000_000;
end Bad_Assign_Rec;
