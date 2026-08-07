procedure Main with SPARK_Mode is

   --  A declare expression is legal in Ada 2022 only, so this unit can only be
   --  analyzed when the switch -gnat2022 of the project file is passed to
   --  gnat2why, in both the global generation and the analysis phases.

   X : constant Integer :=
     (declare
        Y : constant Integer := 1;
      begin
        Y + 1);
begin
   pragma Assert (X = 2);
end Main;
