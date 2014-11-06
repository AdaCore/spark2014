package Justifications with
  SPARK_Mode
is
   procedure Do_Something_1 (X, Y : in out Integer) with
     Depends => ((X, Y) => (X, Y));
   pragma Annotate (GNATprove, Intentional, "incorrect dependency ""Y => X""",
                    "Dependency is kept for compatibility reasons");

   procedure Do_Something_2 (X, Y : in out Integer) with
     Depends => ((X, Y) => (X, Y));

end Justifications;
