with Fake_Socket_Package;

procedure Main is
   X : Integer := 0;
begin
   Fake_Socket_Package.Fake_Sockets (True).Send_Socket (X);
   Fake_Socket_Package.Fake_Sockets (False).Receive_Socket (X);
end;
