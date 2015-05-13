package body Badjustif
  with SPARK_Mode
is
   type A is array (1 .. 10) of Integer;

   procedure P1 is
      X : A;
   begin
      X(1) := 0;
      pragma Annotate
        (GNATprove, False_Positive, """X"" might not be initialized",
         "array X is initialized piecewise");
      for J in 2 .. 10 loop
         X(J) := 1;
      end loop;
   end P1;

   procedure P2 is
      X : Integer := 10;
   begin
      for J in 1 .. 10 loop
         X := X + 1;
      end loop;
   end P2;

end Badjustif;
