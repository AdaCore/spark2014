with Proxy;
with Init;

procedure Main is
begin
   --  Init (False);
   --  If Parent.State is not initialized in elaboration of Parent,
   --  then it can be still initialized by an explicit call to Init.

   pragma Assert (Proxy (False) = 0);
   --  Proxy accesses Parent.State, which should be initialized.
end;
