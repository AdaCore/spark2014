with Prot;

procedure Main is
   X : Integer := Prot.P.F;
   Y : Integer := Prot.P.F;
begin
   pragma Assert (X = Y); --@ASSERT:FAIL
end Main;
