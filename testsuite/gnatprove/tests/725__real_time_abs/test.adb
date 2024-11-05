with Ada.Real_Time; use Ada.Real_Time;

procedure Test with SPARK_Mode is

   procedure Test_Abs (X : Time_Span) is
      V : Time_Span := abs (X);
      pragma Assert (V >= Time_Span_Zero);
      pragma Assert (abs (V) = V);
   begin
      null;
   end Test_Abs;

begin
   null;
end Test;
