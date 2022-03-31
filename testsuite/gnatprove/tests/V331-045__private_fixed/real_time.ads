package Real_Time with
  SPARK_Mode
is
   type Time_Span is private;

   function F return Time_Span;

private

   type Time_Span is new Duration;

end Real_Time;
