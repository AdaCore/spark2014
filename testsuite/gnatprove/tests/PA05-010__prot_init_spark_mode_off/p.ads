package P is

   function Zero return Integer;

   protected type PT is
      function Q return Integer;
   private
      pragma SPARK_Mode (Off);
      X : Integer := 1 / Zero;
   end;

end;
