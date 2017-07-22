package body Fake_Socket_Package is

    protected body Fake_Socket is
        entry Receive_Socket (This : out Integer)
          when Ready
        is
        begin
            This  := Buffer;
            Ready := False;
        end Receive_Socket;

        procedure Send_Socket (This : in Integer)
        is
        begin
            Buffer := This;
            Ready  := True;
        end Send_Socket;

    end Fake_Socket;

end Fake_Socket_Package;
