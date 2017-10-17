procedure Bad_Self_Assign (X : in out Integer) is
   Y : Integer := X - 1;
begin
   X := Y + 1;
end Bad_Self_Assign;
