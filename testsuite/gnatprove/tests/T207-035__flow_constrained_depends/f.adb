procedure F (First, Last :     Integer;
             Data        :     Boolean;
             Result      : out Boolean)
  with Depends => (Result => Data, null => (First, Last))
is
   subtype T is Integer range First .. Last;
begin
   Result := (for some J in T range 1 .. 10 => Data and J = 1);
end;
