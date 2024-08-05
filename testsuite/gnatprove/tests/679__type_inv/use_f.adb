with P1.Child;
procedure Use_F with SPARK_Mode is
begin
   pragma Assert (P1.Child.F2);
   pragma Assert (P1.Child.F1);
end Use_F;
