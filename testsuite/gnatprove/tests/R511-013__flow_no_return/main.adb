with E;

procedure Main is
begin
   E;
   --  Call to procedure with No_Return, but also a Global => (In_Out => ...),
   --  so that it doesn't become "exceptional path" in the flow sense, and the
   --  call doesn't trigger a VC in proof.
end;
