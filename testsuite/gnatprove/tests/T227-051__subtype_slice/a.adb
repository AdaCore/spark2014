procedure A (First, Last :     Integer;
             Data        :     Integer;
             Result      : out Integer)
  with Depends => (Result => Data, null => (First, Last)),
       Post    => Result = Data
is
   subtype S is Integer range First .. Last;
   type T is array (1 .. 10) of Integer;
begin
   Result := T'(S range 1 .. 10 => Data) (1); --@RANGE_CHECK:FAIL
end;
