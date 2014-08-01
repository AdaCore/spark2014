package body Objects with
  SPARK_Mode
is

   procedure Initialize (X : out Object) is
   begin
      X.Position_X := 0;
      X.Position_Y := 0;
      X.Num_Subs   := 0;
   end Initialize;

end Objects;
