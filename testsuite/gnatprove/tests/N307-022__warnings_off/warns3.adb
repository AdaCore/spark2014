procedure Warns3 (X : in out Integer) with
  SPARK_Mode
is
   XXX : Integer;
begin
   XXX := X + 1;
   X := XXX;
   pragma Warnings (GNAT, Off, "useles assignment");
   pragma Warnings (GNATprove, Off, "unuse assignment");
   XXX := XXX + 1;
   pragma Warnings (GNATprove, On, "unuse assignment");
   pragma Warnings (GNAT, On, "useles assignment");
end Warns3;
