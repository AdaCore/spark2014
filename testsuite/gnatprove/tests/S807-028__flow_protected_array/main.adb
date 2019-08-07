with P;
with Q;

procedure Main with Global => (In_Out => Q.X) is
begin
   Q.X (Q.J).Proc;
   --  here we access not only Q.X (an array object), but also Q.J (an index)
end;
