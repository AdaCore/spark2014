function Rec_Constant (X : in Integer) return Integer is
begin
   if X < 10 then
      return 3;
   else
      return Rec_Constant (5);
   end if;
end Rec_Constant;
