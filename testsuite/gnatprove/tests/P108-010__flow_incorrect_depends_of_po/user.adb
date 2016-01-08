with P;

procedure User is
   Tmp : Integer;
begin
   P.The_PO.Set (10);
   Tmp := P.The_PO.Get;

   pragma Assert (Tmp = 10);
end User;
