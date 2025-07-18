package body Simple
with SPARK_Mode
is

   procedure Test_Shape (S : Shape) is
   begin
      pragma Assert (S.Kind = Triangle and then
                       (S.Side1 = S.Side2 and S.Side2 = S.Side3));
   end Test_Shape;

end Simple;
