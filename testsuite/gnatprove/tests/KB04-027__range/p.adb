procedure P (X, Y : Integer) is
   type T is array (X .. Y) of Boolean;
   Z : T := (T'Range => True);
begin
   null;
end P;
