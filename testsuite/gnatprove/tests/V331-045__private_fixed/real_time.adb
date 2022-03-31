package body Real_Time with
  SPARK_Mode => On
is
   function F return Time_Span is
   begin
      return Time_Span (0.0);
   end;

   SC : Integer := Integer (Time_Span'(F));
end Real_Time;
