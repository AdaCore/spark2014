package body P is
   protected body PO is
      procedure Dummy is
      begin
         null;
      end;
   end PO;
begin
   PO.Dummy;
   --  Environment task priority with priority 2 calls a protected operation
   --  with priority 1 => failed check for the ceiling priority protocol.
end P;
