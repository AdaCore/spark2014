procedure Main2 is
   X : Integer;
   procedure P with Address => X'Address, Import;
begin
   null;
end;
