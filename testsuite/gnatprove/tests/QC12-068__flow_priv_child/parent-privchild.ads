with Q;
private package Parent.Privchild
is
   procedure Foo with Global => null;
private
   Child_Private_Var   : Integer := 0;
   Child_Private_Const : constant Integer := Q.F;
end;
