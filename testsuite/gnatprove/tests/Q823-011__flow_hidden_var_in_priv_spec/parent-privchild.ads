with Q;
private package Parent.Privchild
is
   X : Boolean with Part_Of => Parent.State;
   Y : constant Integer := Q.F;
end;
