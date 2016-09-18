with Ada.Real_Time; use Ada.Real_Time;

procedure Main is
   Zero : Integer := 0;
begin
   delay until Time_First + Time_Span_Last / Zero;
end;
