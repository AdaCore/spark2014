with Ada.Real_Time; use Ada.Real_Time;

procedure Main is

   function Div (A : Time_Span; B : Integer) return Time_Span
      with Pre => B /= 0;

   function Div (A : Time_Span; B : Integer) return Time_Span
   is
   begin
      return A / B;
   end Div;

   Zero : Integer := 0;
begin
   delay until Time_First + Div (Time_Span_Last, Zero);
end;
