pragma SPARK_Mode;
procedure Reduced_03
is

   procedure Test_12 (X, Y : Float;
                      Z    : out Float)
     with Pre  => X not in -1.0 .. 1.0
   is
   begin
      Z := X + Y;
   end Test_12;

begin
   null;
end Reduced_03;
