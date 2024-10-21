with Ada.Real_Time; use Ada.Real_Time;
with Ada.Text_IO;

procedure Test with SPARK_Mode is

   procedure Test_Add (X : Time; Y : Time_Span) is
      V1 : Time := X + Y; -- @RANGE_CHECK:FAIL
      V2 : Time := Y + X;
      pragma Assert (V1 = V2);
      V3 : Time_Span := Y + Y; -- @RANGE_CHECK:FAIL
      pragma Assert (V3 = 2 * Y);
      pragma Assert (Y = 1 * Y);
   begin
      null;
   end Test_Add;

   procedure Test_Subst (X1, X2 : Time; Y1, Y2 : Time_Span) is
      V1 : Time := X1 - Y1; -- @RANGE_CHECK:FAIL
      V2 : Time_Span := X1 - X2; -- @RANGE_CHECK:FAIL
      V3 : Time_Span := Y1 - Y2; -- @RANGE_CHECK:FAIL
      V4 : Time_Span := - Y1; -- @RANGE_CHECK:FAIL
   begin
      null;
   end Test_Subst;

   procedure Test_Mult (X : Time_Span; Y : Integer) is
      V1 : Time_Span := X * Y; -- @RANGE_CHECK:FAIL
      V2 : Time_Span := Y * X;
      pragma Assert (V1 = V2);
   begin
      null;
   end Test_Mult;

   procedure Test_Div (X : Time_Span; Y : Time_Span; Z : Integer) is
      V1 : Integer := X / Y; -- @RANGE_CHECK:FAIL @DIVISION_CHECK:FAIL
      V2 : Time_Span := X / Z; -- @RANGE_CHECK:FAIL @DIVISION_CHECK:FAIL
      pragma Assert (Y / 1 = Y);
      pragma Assert (if Y /= Time_Span_Zero then Y / Y = 1);
   begin
      null;
   end Test_Div;

   procedure Test_Lt (X1, X2 : Time; Y1, Y2 : Time_Span) is
      B1 : Boolean := X1 < X2;
      pragma Assert (if B1 then not (X2 < X1));
      pragma Assert (not (X1 < X1));
      B2 : Boolean := Y1 < Y2;
      pragma Assert (if B2 then not (Y2 < Y1));
      pragma Assert (not (Y1 < Y1));
   begin
      null;
   end Test_Lt;

   procedure Test_Le (X1, X2 : Time; Y1, Y2 : Time_Span) is
      B1 : Boolean := X1 <= X2;
      pragma Assert (if B1 and X2 <= X1 then X1 = X2);
      pragma Assert (X1 <= X1);
      B2 : Boolean := Y1 <= Y2;
      pragma Assert (if B2 and Y2 <= Y1 then Y1 = Y2);
      pragma Assert (Y1 <= Y1);
   begin
      pragma Assert (X1 <= Time_Last);
   end Test_Le;

   procedure Test_Gt (X1, X2 : Time; Y1, Y2 : Time_Span) is
      B1 : Boolean := X1 > X2;
      pragma Assert (if B1 then not (X2 > X1));
      pragma Assert (not (X1 > X1));
      B2 : Boolean := Y1 > Y2;
      pragma Assert (if B2 then not (Y2 > Y1));
      pragma Assert (not (Y1 > Y1));
   begin
      null;
   end Test_Gt;

   procedure Test_Ge (X1, X2 : Time; Y1, Y2 : Time_Span) is
      B1 : Boolean := X1 >= X2;
      pragma Assert (if B1 and X2 >= X1 then X1 = X2);
      pragma Assert (X1 >= X1);
      B2 : Boolean := Y1 >= Y2;
      pragma Assert (if B2 and Y2 >= Y1 then Y1 = Y2);
      pragma Assert (Y1 >= Y1);
   begin
      pragma Assert (X1 >= Time_First);
   end Test_Ge;

   procedure Test_Seconds (I : Integer) is
      V : Time_Span := Seconds (I);
   begin
      pragma Assert (V = (Time_Span_Unit * I) * Integer (1.0 / Time_Unit));
   end Test_Seconds;

   procedure Test_Minutes (I : Integer) is
      V : Time_Span := Minutes (I); -- @RANGE_CHECK:FAIL
   begin
      pragma Assert (V = 60 * Seconds (I));
   end Test_Minutes;

   procedure Test_Milliseconds (I : Integer) is
      V : Time_Span := Milliseconds (I);
   begin
      pragma Assert (V * 1_000 = Seconds (I));
   end Test_Milliseconds;

   procedure Test_Microseconds (I : Integer) is
      V : Time_Span := Microseconds (I);
   begin
      pragma Assert (V * 1_000_000 = Seconds (I));
   end Test_Microseconds;

   procedure Test_Nanoseconds (I : Integer) is
      V : Time_Span := Nanoseconds (I);
   begin
      pragma Assert (V * 1_000_000_000 = Seconds (I));
   end Test_Nanoseconds;

   procedure Test_To_Duration (X : Time_Span) is
      V1 : Duration := To_Duration (X);
      V2 : Duration := To_Duration (Time_Span_Unit);
   begin
      pragma Assert (V2 = Time_Unit);
   end Test_To_Duration;

   procedure Test_To_Time_Span (X : Duration) is
      V1 : Time_Span := To_Time_Span (X);
      V2 : Time_Span := To_Time_Span (Time_Unit);
   begin
      pragma Assert (V2 = Time_Span_Unit);
   end Test_To_Time_Span;

   procedure Test_Split_And_Time_Of is
      Sc : Seconds_Count;
      Ts : Time_Span;
   begin
      Split (Time_Of (2, Milliseconds (600)), Sc, Ts);
      pragma Assert (Sc = 2);
      pragma Assert (Ts = Milliseconds (600));
      Split (Time_Of (-2, Milliseconds (-600)), Sc, Ts);
      pragma Assert (Sc = -3);
      pragma Assert (Ts = Milliseconds (400));
   end Test_Split_And_Time_Of;

   C  : constant := 9223372036854775807.0;
begin
   pragma Assert (Time_First <= Time_Of (0, Time_Span_Zero));
   pragma Assert (Time_Last >= Time_Of (0, To_Time_Span (C * Time_Unit)));
   pragma Assert (Time_Span_First <= To_Time_Span (- C * Time_Unit));
   pragma Assert (Time_Span_Last >= To_Time_Span (C * Time_Unit));
end Test;
