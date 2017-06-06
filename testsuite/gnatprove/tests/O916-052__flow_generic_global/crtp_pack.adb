package body CRTP_Pack is

   procedure CRTP_Append_Data
     (Handler : in out CRTP_Packet_Handler)
   is
   begin
      Handler.Index := Handler.Index + 0;
   end CRTP_Append_Data;

end CRTP_Pack;
