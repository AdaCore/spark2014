with Misc_Binding; use Misc_Binding;

procedure Connect (Sock : in out Not_Null_Socket) is
begin
   Send_Segment (Sock);
end Connect;
