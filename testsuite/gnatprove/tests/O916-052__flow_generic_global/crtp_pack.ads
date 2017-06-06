package CRTP_Pack is

   type CRTP_Packet_Handler is private;

   generic
      type T_Data is private;
   procedure CRTP_Append_Data
     (Handler : in out CRTP_Packet_Handler);

private

   type CRTP_Packet_Handler is record
      Index : Positive;
   end record;

end CRTP_Pack;
