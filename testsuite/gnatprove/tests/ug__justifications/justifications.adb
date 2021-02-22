package body Justifications with
  SPARK_Mode
is
   procedure Do_Something_1 (X, Y : in out Integer) is
   begin
      X := X + Y;
      Y := Y + 1;
   end Do_Something_1;

   procedure Do_Something_2 (X, Y : in out Integer) is
   begin
      X := X + Y;
      Y := Y + 1;
   end Do_Something_2;
   pragma Annotate (GNATprove, Intentional, "incorrect dependency ""Y => X""",
                    "Currently Y does not depend on X, but may change later");

end Justifications;
