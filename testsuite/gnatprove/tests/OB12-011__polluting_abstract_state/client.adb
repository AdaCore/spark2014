with P;

procedure Client is
   X : Integer;
begin
   P.PO.Dummy;
   X := 1;
   pragma Assert (X > 0); --  Just to generate a dummy VC
end;
