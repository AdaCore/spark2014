procedure Old_Val with
  SPARK_Mode
is
   subtype T is Integer range 1 .. 10;

   procedure Local (X, Y : T) with
     Post => Natural'(X - Y)'Old /= 0 or else True
   is
   begin
      null;
   end Local;
begin
   Local (1, 2);
end Old_Val;
