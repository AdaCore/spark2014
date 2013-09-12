with N.K;

procedure Main is pragma SPARK_Mode (Off);
   Specific_A  : N.K.P;
   ClassWide_A : N.K.P'Class := Specific_A;
begin
   null;
end Main;
