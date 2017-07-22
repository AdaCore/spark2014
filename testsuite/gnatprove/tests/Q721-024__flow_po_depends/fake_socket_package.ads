package Fake_Socket_Package is

    protected type Fake_Socket is
        entry Receive_Socket (This : out Integer)
        with Depends => ((This, Fake_Socket) => Fake_Socket);

        procedure Send_Socket (This: in Integer)
        with Depends => (Fake_Socket => (Fake_Socket, This));

    private
        Ready : Boolean := False;
        Buffer: Integer := 0;
    end Fake_Socket;

    Fake_Sockets : array (Boolean) of Fake_Socket;

end Fake_Socket_Package;
