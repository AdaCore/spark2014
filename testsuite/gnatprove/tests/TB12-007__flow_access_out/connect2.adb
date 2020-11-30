with Misc_Binding; use Misc_Binding;

procedure Connect2 (Sock : in out Not_Null_Socket)
   with Depends => (Sock => Sock)
is
begin
   Send_Segment2 (Sock);
end Connect2;
