with P;

procedure Main is
   pragma Priority (2);
begin
   P.PO.Dummy;
   --  Environment task priority with priority 2 calls a protected operation
   --  with priority 1 => failed check for the ceiling priority protocol.
end;
