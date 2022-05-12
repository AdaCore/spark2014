procedure Warns2 (X : in out Integer) with
  SPARK_Mode
is
   XXX : Integer;
begin
   XXX := X + 1;
   X := XXX;
   pragma Warnings (Off, "useless assignment");
   XXX := XXX + 1;
   pragma Warnings (On, "useless assignment");
end Warns2;
