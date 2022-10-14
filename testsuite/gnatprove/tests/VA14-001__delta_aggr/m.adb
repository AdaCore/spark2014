procedure M is
   type T is array (1 .. 3) of Integer;
   Y : T := (others => 0);
   Z : T := [Y with delta 3 => 1];
begin
   null;
end;
