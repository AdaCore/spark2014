with A;

procedure Main is
   Result : Integer;
begin
   A (First => 2, Last => 9, Data => 3, Result => Result);
   pragma Assert (Result = 3);
end;
