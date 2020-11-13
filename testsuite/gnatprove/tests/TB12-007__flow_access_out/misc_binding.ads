package Misc_Binding is

   type Socket is access Integer;
   subtype Not_Null_Socket is not null Socket;

   procedure Send_Segment (Sock : in Not_Null_Socket) with
      Depends => (Sock => Sock);

   procedure Send_Segment2 (Sock : in Not_Null_Socket);

end Misc_Binding;
