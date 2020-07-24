pragma Warnings (Off, "unused initial value of ""X""",
                 Reason => "Parameter mode is mandated by API");

procedure Warn (X : in out Integer) with
  SPARK_Mode
is
   pragma Warnings (Off, "initialization has no effect",
                    Reason => "Coding standard requires initialization");
   Y : Integer := 0;
   pragma Warnings (On, "initialization has no effect");

begin
   pragma Warnings (Off, "unused assignment",
                    Reason => "Test program requires double assignment");
   X := Y;
   pragma Warnings (On, "unused assignment");
   X := Y;
end Warn;
