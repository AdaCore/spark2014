procedure P (First, Last :     Integer;
             Data        :     Integer;
             Result      : out Integer)
  with Depends => (Result => Data, null => (First, Last))
is
   subtype T is Integer range First .. Last;
begin
   Result := T'(Data);
end;
