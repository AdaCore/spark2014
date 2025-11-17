package body P is

   procedure Test_Rec (S : Rec) is
   begin
      pragma Assert (S.Kind = 'B' and then (S.Y = S.Z));
   end;

end P;
