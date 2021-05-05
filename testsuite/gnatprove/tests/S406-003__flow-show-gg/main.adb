with Entity_Name;

procedure Main
   --  Entity_Name.Hidden is Global so we should generate contract:
   --    with Global => (Input => Entity_Name.Hidden)
is
   X : Boolean := Entity_Name.Proxy;
begin
   null;
end Main;
