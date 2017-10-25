private package P.Priv_Child is
   C : constant Integer := V; -- needs Part_Of
   D : constant Integer := V with Part_Of => P.State;
   procedure Foo;
end;
