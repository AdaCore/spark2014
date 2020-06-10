procedure Min (Low, High, X, Y : Integer; Result : out Integer)
  with Depends => (Result => (X, Y), null => (Low, High)),
       Post    => Result = Integer'Min (X, Y)
is
   subtype S is Integer range Low .. High;
begin
   Result := S'Min (X, Y);
end;
