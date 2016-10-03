with P;

procedure Main is
   -- call to protected function with composite prefixes
   X : Boolean := P.PO1.C.F;
   Y : Boolean := P.Po2 (True).F;
begin
   null;
end;
