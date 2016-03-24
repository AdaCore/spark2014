with Pack; use Pack;

procedure Use_Pack is
   C : Child;
begin
   C := (F1 => 0, F2 => Integer'Last);
   C.Incr;  --  @PRECONDITION:PASS

   C := (F1 => 0, F2 => Integer'Last);
   C.Incr2;  --  @PRECONDITION:FAIL
end Use_Pack;
