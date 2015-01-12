procedure Warns2 (X : in out Integer) with
  SPARK_Mode
is
   Tmp : Integer;
begin
   Tmp := X + 1;
   X := Tmp;
   pragma Warnings (Off, "useless assignment");
   Tmp := Tmp + 1;
   pragma Warnings (On, "useless assignment");
end Warns2;
