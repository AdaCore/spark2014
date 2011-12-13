procedure P is
   type T is array (1 .. 2, 1 .. 2) of Boolean;
   X : T;
begin
   X (1, 1) := True;
end P;
