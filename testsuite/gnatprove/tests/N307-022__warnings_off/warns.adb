procedure Warns (X : in out Integer) with
  SPARK_Mode
is
   Tmp : Integer;
begin
   Tmp := X + 1;
   X := Tmp;
   pragma Warnings (GNAT, Off, "useless assignment");
   pragma Warnings (GNATprove, Off, "unused assignment");
   Tmp := Tmp + 1;
   pragma Warnings (GNATprove, On, "unused assignment");
   pragma Warnings (GNAT, On, "useless assignment");
end Warns;
