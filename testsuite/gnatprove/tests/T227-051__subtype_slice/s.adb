procedure S (First, Last :     Integer;
             Data        :     Integer;
             Result      : out Integer)
  with Depends => (Result => Data, null => (First, Last)),
       Post    => Result = Data
is
   subtype S is Integer range First .. Last;
   type T is array (1 .. 10) of Integer;
   X : T := (others => Data);
begin
   Result := X (S range 1 .. 10) (1);
end;
