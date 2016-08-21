procedure Len (Last : Integer) is
   type T is Array (1 .. Last) of Integer;
begin
   pragma Assert (T'Length = 0);
end;
