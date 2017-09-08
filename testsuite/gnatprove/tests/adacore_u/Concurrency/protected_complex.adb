package body Protected_Complex
  with SPARK_Mode
is
   Data : Boolean := False;

   protected body P is
      entry Reset when Data is
      begin
         null;
      end Reset;
   end P;

end Protected_Complex;
