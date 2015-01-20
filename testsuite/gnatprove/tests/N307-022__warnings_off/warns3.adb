procedure Warns3 (X : in out Integer) with
  SPARK_Mode
is
   Tmp : Integer;
begin
   Tmp := X + 1;
   X := Tmp;
   pragma Warnings (GNAT, Off, "useles assignment");
   pragma Warnings (GNATprove, Off, "unuse assignment");
   Tmp := Tmp + 1;
   pragma Warnings (GNATprove, On, "unuse assignment");
   pragma Warnings (GNAT, On, "useles assignment");
end Warns3;
