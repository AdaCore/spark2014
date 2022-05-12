procedure Warns (X : in out Integer) with
  SPARK_Mode
is
   Tmp : Integer;
begin
   Tmp := X + 1;
   X := Tmp;
   pragma Warnings (GNATprove, Off, "unused assignment");
   Tmp := Tmp + 1;
   pragma Warnings (GNATprove, On, "unused assignment");
end Warns;
